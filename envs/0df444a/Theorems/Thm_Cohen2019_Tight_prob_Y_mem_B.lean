-- Prove2me | Theorems.Thm_Cohen2019_Tight_prob_Y_mem_B
-- name    : Cohen2019.Tight.prob_Y_mem_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:30:51.074993+00:00
-- url     : https://prove2.me/theorems/55725a81-ec39-4350-b02b-466ac6ac7ca1
-- title:
--   Eq. (14) — ℙ(Y ∈ B) = Φ(Φ⁻¹(p_B) + ‖δ‖/σ) for Y ∼ 𝒩(x + δ, σ²I)
-- statement:
--   Let $\sigma>0$, $x,\delta\in\mathbb R^d$ with $\delta\ne0$, and $0<\overline{p_B}<1$. Let $Y\sim\mathcal N(x+\delta,\sigma^2I)$ and let $B$ be the half-space $\{z:\delta^T(z-x)\ge\sigma\|\delta\|\Phi^{-1}(1-\overline{p_B})\}$. Then
--   $$\mathbb P(Y\in B)=\Phi\Big(\Phi^{-1}(\overline{p_B})+\frac{\|\delta\|}{\sigma}\Big).$$
--
--   Shifting the Gaussian by $\delta$ moves mass into $B$ at a rate governed only by $\|\delta\|/\sigma$.
--
--   **Formalization Note.** $\delta\ne0$ and $0<\overline{p_B}<1$ are added.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A, eq. (14), p. 14; proved as the Claim in Appendix A.0.1, p. 16

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, Appendix A, (14), p. 14 (proved as the
Claim `ℙ(Y ∈ B) = Φ(Φ⁻¹(p̄B) + ‖δ‖/σ)`, Appendix A.0.1, p. 16): for `Y ∼ 𝒩(x + δ, σ²I)`,
`ℙ(Y ∈ B) = Φ(Φ⁻¹(p̄B) + ‖δ‖/σ)`.

**Formalization Note.** `δ ≠ 0` and `0 < p̄B < 1` are added, as for `prob_X_mem_B`. -/
theorem prob_Y_mem_B {d : ℕ} (x δ : Space d) (σ pB : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise (x + δ) σ (setB x δ σ pB)).toReal = Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal pB + ‖δ‖ / σ) := by sorry

end Cohen2019.Tight
