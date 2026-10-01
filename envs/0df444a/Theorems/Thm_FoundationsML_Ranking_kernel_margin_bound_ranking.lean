-- Prove2me | Theorems.Thm_FoundationsML_Ranking_kernel_margin_bound_ranking
-- name    : FoundationsML.Ranking.kernel_margin_bound_ranking
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:03:17.512985+00:00
-- url     : https://prove2.me/theorems/8bbe195e-d0e4-45be-b540-b6ea32eeee78
-- title:
--   Corollary 10.2 — Margin bound for ranking with kernel-based hypotheses
-- statement:
--   **Statement (Corollary 10.2, p. 243, PDF p. 260).** Let $K$ be a PDS kernel with
--   $r=\sup_{x\in X}K(x,x)$, feature map $\Phi$, and $H=\{x\mapsto w\cdot\Phi(x):
--   \|w\|_H\le\Lambda\}$. Fix $\rho>0$. Then, for any $\delta>0$, with probability at least
--   $1-\delta$, for all $h\in H$: $R(h) \le \hat R_{S,\rho}(h) + 4\sqrt{r^2\Lambda^2/\rho^2/m} +
--   \sqrt{\log(1/\delta)/(2m)}$.
--
--   **Formalization Note.** `r` is taken as an upper bound on `K(x,x)` (`hrK`) rather than
--   literally computing `sup_x K(x,x)`, per `BRIEF.md`'s pitfall note about the possibly
--   infinite supremum — the theorem only needs `r` to bound the kernel diagonal, and the
--   conclusion is monotonic in `r`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 243, Corollary 10.2 (PDF p. 260)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_IsPDS
import Definitions.Def_FoundationsML_Ranking_LinearKernelHypothesisClass

open MeasureTheory

namespace FoundationsML.Ranking

/-- Corollary 10.2 (Margin bound for ranking with kernel-based hypotheses; Mohri, Rostamizadeh
& Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 243, PDF p. 260).
Let `K` be a PDS kernel with feature map `Φ` and `r` an upper bound on `K(x,x)` (the book's
`r = sup_x K(x,x)`), and `H = {x ↦ w·Φ(x) : ‖w‖_H ≤ Λ}`. Fix `ρ > 0`. Then, for any `δ > 0`,
with probability at least `1 − δ`, for all `h ∈ H`:
`R(h) ≤ R̂_{S,ρ}(h) + 4·sqrt(r²Λ²/ρ²/m) + sqrt(log(1/δ)/(2m))`. -/
theorem kernel_margin_bound_ranking
    {X Hb : Type*} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 ≤ r) (hrK : ∀ x, K x x ≤ r)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ LinearKernelHypothesisClass Φ Λ,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            4 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Ranking
