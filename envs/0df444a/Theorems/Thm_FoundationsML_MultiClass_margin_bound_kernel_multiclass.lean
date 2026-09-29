-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_margin_bound_kernel_multiclass
-- name    : FoundationsML.MultiClass.margin_bound_kernel_multiclass
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T23:34:58.178974+00:00
-- url     : https://prove2.me/theorems/0f2d6d83-e3e1-41bf-b292-1575c713da64
-- title:
--   Corollary 9.4 — Margin bound for kernel-based multi-class hypotheses
-- statement:
--   **Statement (Corollary 9.4, p. 220, PDF p. 237).** Under Proposition 9.3's hypotheses on
--   $K,\Phi,r$, fix $\rho>0$. Then, for any $\delta>0$, with probability at least $1-\delta$,
--   for all $h\in H_{K,p}$: $R(h) \le \hat R_{S,\rho}(h) + 4k\sqrt{r^2\Lambda^2/\rho^2/m} +
--   \sqrt{\log(1/\delta)/(2m)}$. Obtained by substituting Proposition 9.3's bound directly into
--   Theorem 9.2.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 220, Corollary 9.4 (PDF p. 237)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Corollary 9.4 (Margin bound for multi-class classification with kernel-based hypotheses;
Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 220, PDF p. 237). Under Proposition 9.3's hypotheses on `K`, `Φ`, `r`, fix `ρ > 0`. Then,
for any `δ > 0`, with probability at least `1 − δ`, the following holds for all
`h ∈ H_{K,p}`: `R(h) ≤ R̂_{S,ρ}(h) + 4k sqrt(r²Λ²/ρ²/m) + sqrt(log(1/δ)/(2m))`. -/
theorem margin_bound_kernel_multiclass
    {X Hb : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk2 : 2 ≤ k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ)
    (f : X → Fin k) (m : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ KernelHypothesisClass Φ k p Λ, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + 4 * (k : ℝ) * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
