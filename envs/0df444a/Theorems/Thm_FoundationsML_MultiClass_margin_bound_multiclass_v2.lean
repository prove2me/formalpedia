-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_margin_bound_multiclass_v2
-- name    : FoundationsML.MultiClass.margin_bound_multiclass_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:40.10299+00:00
-- url     : https://prove2.me/theorems/91747d1b-3d9a-42fc-95aa-60785762c524
-- title:
--   Theorem 9.2 — margin bound for multi-class classification (goal; corrected margin, $m\ge1$)
-- statement:
--   **Statement (Theorem 9.2, p. 217, PDF p. 234).** Let $H\subseteq\mathbb R^{X\times Y}$ be a bounded hypothesis set with $Y=\{1,\dots,k\}$, $k\ge2$, and $f:X\to Y$ a (measurable) target. Fix $\rho>0$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, for all $h\in H$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac{4k}\rho R_m(\Pi_1(H)) + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$). Changes: $m\ge1$, $\delta\in(0,1)$ (standing conventions); the margin $\rho_h(x,y)=h(x,y)-\max_{y'\ne y}h(x,y')$, the risk $R(h)=\Pr[\rho_h(x,f(x))\le0]$ and $\hat R_{S,\rho}$ are the corrected `MarginFunction`/`GeneralizationError`/`EmpiricalMarginLoss` (`_v2`, maximum over exactly the labels $y'\neq y$ — the retired `⨆ y' ∈ {y' ≠ y}` was clipped at $0$ and is not the book's margin when all competing scores are negative); the Rademacher complexity is the corrected `RademacherComplexity` (`_v2`, supremum over exactly $\Pi_1(H)$); the book's standing measurability of the target $f$ (footnote 2, p. 10) and of the supremum defining $\hat R_S(\Pi_1(H))$ (footnote 3, p. 30, needed for $R_m$ to be the book's expectation rather than Lean's junk $0$) are explicit. Bounded $H$ (Definition 3.1's domain) and measurability of the sections $x\mapsto h(x,y)$ are as before.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 217, Theorem 9.2 (PDF p. 234)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError_v2
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss_v2
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity_v2

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Theorem 9.2 (Margin bound for multi-class classification; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 217, PDF p. 234).
Let `H ⊆ ℝ^{X×Y}` be a (bounded) hypothesis set with `Y = {1,…,k}` (here `Fin k`, `k ≥ 2`).
Fix `ρ > 0`. Then, for any `δ > 0`, with probability at least `1 − δ` over an i.i.d. sample
of size `m ≥ 1`, the following holds for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + (4k/ρ) R_m(Π_1(H)) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `margin_bound_multiclass`, which allowed `m = 0` (every
sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)` (standing
conventions); the margin `ρ_h`, the risk and the empirical margin loss are the corrected
`MarginFunction`/`GeneralizationError`/`EmpiricalMarginLoss` (`_v2`, maximum over exactly the
labels `y' ≠ y` — the retired `⨆ y' ∈ {y' ≠ y}` was clipped at `0`); the Rademacher
complexity is the corrected `RademacherComplexity` (`_v2`, supremum over exactly `Π_1(H)`);
the book's standing measurability of the target `f` (footnote 2, p. 10) and of the supremum
defining `R̂_S(Π_1(H))` (footnote 3, p. 30, `hHsup`, needed for `R_m` to be the book's
expectation rather than Lean's junk `0`) are explicit. `hHb` (bounded `H`, Definition 3.1's
domain for `R_m`) and `hHmeas` (measurability of the sections of `h ∈ H`) are as before. -/
theorem margin_bound_multiclass_v2
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (k : ℕ) (hk : 2 ≤ k) (f : X → Fin k) (hf : Measurable f) (H : Set (X × Fin k → ℝ))
    (hHb : ∃ M : ℝ, ∀ h ∈ H, ∀ z : X × Fin k, |h z| ≤ M)
    (hHmeas : ∀ h ∈ H, ∀ y : Fin k, Measurable (fun x => h (x, y)))
    (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity (Proj1 H) S))
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + (4 * (k : ℝ) / ρ) * RademacherComplexity D (Proj1 H) m +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
