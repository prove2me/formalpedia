-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_rademacher_generalization_bound_v2
-- name    : FoundationsML.RademacherVC.rademacher_generalization_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:45.007881+00:00
-- url     : https://prove2.me/theorems/94e711f6-6c86-47f0-aeae-0367809d6d11
-- title:
--   Theorem 3.3 — Rademacher-complexity generalization bounds (3.3) and (3.4)
-- statement:
--   **Statement (Theorem 3.3, p. 31, PDF p. 48).** Let $G$ be a family of (measurable) functions mapping from $Z$ to $[0,1]$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over the draw of an i.i.d. sample $S$ of size $m\ge1$, each of the following holds for all $g\in G$:
--   $$\mathbb E[g(z)] \le \frac1m\sum_{i=1}^m g(z_i) + 2R_m(G) + \sqrt{\frac{\log(1/\delta)}{2m}}, \qquad (3.3)$$
--   $$\mathbb E[g(z)] \le \frac1m\sum_{i=1}^m g(z_i) + 2\hat R_S(G) + 3\sqrt{\frac{\log(2/\delta)}{2m}}. \qquad (3.4)$$
--   Each inequality holds with probability at least $1-\delta$ (the book proves them separately).
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is then Lean's $x/0=0$ and the bound is false) and stated only (3.3). New statement: $m\ge1$ and $\delta\in(0,1)$ (standing conventions); both displayed inequalities, as a conjunction of two probability statements; the empirical Rademacher complexity is the corrected `EmpiricalRademacherComplexity` (`_v2`, supremum over exactly $G$ — the retired `⨆ g ∈ G` clipped negative suprema at $0$); and the book's footnote 3 (p. 30), "we assume implicitly that the supremum over the family $G$ in this definition is measurable", is an explicit hypothesis `Measurable (fun S => R̂_S(G))`. Without it the Bochner integral defining $R_m(G)$ silently returns $0$ and the statement is false (take $G=\{1-\mathbf 1_F : F\subseteq A \text{ finite}\}\cup\{1-\mathbf 1_F : F\subseteq A^c\text{ finite}\}$ for a non-measurable $A\subseteq[0,1]$: $\hat R_S(G)$ is not a.e.-measurable, so $R_m(G)=0$ in Lean while $\sup_g(\mathbb E g-\hat{\mathbb E}_S g)\ge1/2$ for every $S$). Measurability of each $g\in G$ is footnote 2's convention (p. 10). The probability of the event $\{S\mid\forall g\in G,\dots\}$ is its `Measure.pi`-measure (outer measure if not measurable); the book's footnote also licenses assuming the suprema in the proof measurable, which is not encoded beyond $\hat R_S(G)$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 31, Theorem 3.3 (PDF p. 48)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Theorem 3.3 (Rademacher-complexity generalization bounds; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 31, PDF p. 48).
Let `G` be a family of functions mapping from `Z` to `[0,1]`. Then, for any `δ > 0`, with
probability at least `1 − δ` over the draw of an i.i.d. sample `S` of size `m ≥ 1`, each of
the following holds for all `g ∈ G`:
`E[g(z)] ≤ (1/m) ∑_{i=1}^m g(z_i) + 2 R_m(G) + sqrt(log(1/δ)/(2m))`   (3.3)
and `E[g(z)] ≤ (1/m) ∑_{i=1}^m g(z_i) + 2 R̂_S(G) + 3 sqrt(log(2/δ)/(2m))`   (3.4).

**Formalization Note.** Replaces `rademacher_generalization_bound`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`) and stated only (3.3). Now: `m ≥ 1`
and `δ ∈ (0,1)` (the book's standing conventions); both displayed inequalities (3.3) and (3.4),
each holding with probability at least `1 − δ` (the book proves them separately, each at
confidence `1 − δ`); the empirical Rademacher complexity is the corrected
`EmpiricalRademacherComplexity` (`_v2`, supremum over exactly `G`); and the book's footnote 3
(p. 30), "the supremum over the family `G` in this definition is measurable", is made explicit
as `hGsup`, without which the Bochner integral defining `R_m(G)` silently returns `0`. `hGm`
is the standing measurability of the functions in `G` (footnote 2, p. 10). -/
theorem rademacher_generalization_bound_v2
    {Z : Type*} [MeasurableSpace Z] (D : Measure Z) [IsProbabilityMeasure D]
    (G : Set (Z → ℝ)) (hGb : ∀ g ∈ G, ∀ z, g z ∈ Set.Icc (0 : ℝ) 1)
    (hGm : ∀ g ∈ G, Measurable g)
    (m : ℕ) (hm : 0 < m)
    (hGsup : Measurable (fun S : Fin m → Z => EmpiricalRademacherComplexity G S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * RademacherComplexity D G m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → Z | ∀ g ∈ G, (∫ z, g z ∂D) ≤
        (1 / (m : ℝ)) * ∑ i, g (S i) + 2 * EmpiricalRademacherComplexity G S +
          3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC
