-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_rademacher_generalization_bound
-- name    : FoundationsML.RademacherVC.rademacher_generalization_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:13:42.455895+00:00
-- url     : https://prove2.me/theorems/52f0eb32-7eae-45b8-b183-19b98752c078
-- title:
--   Theorem 3.3 — Rademacher-complexity generalization bound
-- statement:
--   **Statement (Theorem 3.3, p. 31, PDF p. 48).** Let $G$ be a family of functions mapping
--   from $Z$ to $[0,1]$. Then, for any $\delta>0$, with probability at least $1-\delta$ over an
--   i.i.d. sample $S$ of size $m$, for all $g\in G$:
--   $$\mathbb E[g(z)] \le \frac1m\sum_{i=1}^m g(z_i) + 2R_m(G) + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   This is the chapter's first generalization bound for possibly-infinite function families,
--   proved via McDiarmid's inequality applied to the deviation $\sup_{g\in G}(\mathbb E[g]-
--   \hat{\mathbb E}_S[g])$.
--
--   **Formalization Note.** `G` bounded in `[0,1]` and measurable (`hGb`, `hGm` — the latter is
--   the book's own standing measurability assumption, footnote 3, p. 30, made explicit here to
--   avoid the Bochner-integral trap of a non-integrable `∫ z, g z ∂D` silently evaluating to
--   `0`); the bound is stated for every `g ∈ G` inside the same probability event (uniform
--   convergence), matching "each of the following holds for all `g ∈ G`."
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Theorem 3.3 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Theorem 3.3 (Rademacher-complexity generalization bound; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 31, PDF p. 48).
Let `G` be a family of measurable functions mapping from `Z` to `[0,1]`. Then, for any
`δ > 0`, with probability at least `1 − δ` over the draw of an i.i.d. sample `S` of size `m`,
each of the following holds for all `g ∈ G`:
`E[g(z)] ≤ (1/m) ∑_{i=1}^m g(z_i) + 2 R_m(G) + sqrt(log(1/δ)/(2m))`. -/
theorem rademacher_generalization_bound
    {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC
