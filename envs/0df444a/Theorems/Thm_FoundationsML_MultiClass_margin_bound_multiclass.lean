-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_margin_bound_multiclass
-- name    : FoundationsML.MultiClass.margin_bound_multiclass
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:33:26.5434+00:00
-- url     : https://prove2.me/theorems/6876573a-1d41-406c-803b-548930dfa14b
-- title:
--   Theorem 9.2 — Margin bound for multi-class classification (goal)
-- statement:
--   **Statement (Theorem 9.2, p. 217, PDF p. 234).** Let $H\subseteq\mathbb R^{X\times Y}$ be a
--   hypothesis set with $Y=\{1,\dots,k\}$. Fix $\rho>0$. Then, for any $\delta>0$, with
--   probability at least $1-\delta$, for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \tfrac{4k}\rho R_m(\Pi_1(H)) + \sqrt{\tfrac{\log(1/\delta)}
--   {2m}}.$$
--   This is the chapter's answer to extending the binary margin bound (chunk `05-svm`'s Theorem
--   5.8) to $k$ classes: the same Rademacher-complexity machinery, but with an extra factor of
--   $4k$ that makes the class-count dependence explicit.
--
--   **Formalization Note.** `Y = Fin k` with `hk : 2 ≤ k` (mono-label multi-class needs at
--   least two classes, guarding `MarginFunction`'s `⨆` against trap 5); `Π_1(H)` (not `H`) is
--   what `RademacherComplexity` is applied to, per `BRIEF.md`'s pitfall note; `R̂_{S,ρ}` is this
--   chapter's own `EmpiricalMarginLoss`, not chunk `05`'s binary one.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 217, Theorem 9.2 (PDF p. 234)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Theorem 9.2 (Margin bound for multi-class classification; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 217, PDF p. 234).
Let `H ⊆ ℝ^{X×Y}` be a hypothesis set with `Y = {1,…,k}` (here `Fin k`, `k ≥ 2`). Fix `ρ > 0`.
Then, for any `δ > 0`, with probability at least `1 − δ`, the following holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (4k/ρ) R_m(Π_1(H)) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** `hHb`/`hHmeas` guard `RademacherComplexity D (Proj1 H) m` against trap
2, mirroring chunk `03-rademacher-vc`'s `rademacher_generalization_bound` (its own consumer of
this chunk's `EmpiricalRademacherComplexity`/`RademacherComplexity`-shaped definitions), whose
`hGb`/`hGm` guard the same `⨆`/`∫` pattern. Without them, an unbounded `H` collapses
`RademacherComplexity D (Proj1 H) m` to Lean's junk value `0` (real `⨆`/`sSup` of an
unbounded-above set is `0`, not `+∞`), making the theorem's conclusion a small finite quantity
rather than the vacuously-true bound the book's implicit "well-defined complexity" reading
gives — false, not merely unprovable, for such `H`. `hHmeas` states measurability of `Proj1 H`'s
elements directly (`fun x => h (x, y)` for `h ∈ H`, `y : Fin k`), avoiding a need for a
`MeasurableSpace (Fin k)` instance that `RademacherComplexity`'s own signature (over `X`, not
`X × Fin k`) does not otherwise require. -/
theorem margin_bound_multiclass
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (k : ℕ) (hk : 2 ≤ k) (f : X → Fin k) (H : Set (X × Fin k → ℝ))
    (hHb : ∃ M : ℝ, ∀ h ∈ H, ∀ z : X × Fin k, |h z| ≤ M)
    (hHmeas : ∀ h ∈ H, ∀ y : Fin k, Measurable (fun x => h (x, y)))
    (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + (4 * (k : ℝ) / ρ) * RademacherComplexity D (Proj1 H) m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
