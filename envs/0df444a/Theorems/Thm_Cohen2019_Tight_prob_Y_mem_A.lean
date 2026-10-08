-- Prove2me | Theorems.Thm_Cohen2019_Tight_prob_Y_mem_A
-- name    : Cohen2019.Tight.prob_Y_mem_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:30:54.450684+00:00
-- url     : https://prove2.me/theorems/922bfb3c-030b-45bc-9be5-6507bebd355b
-- title:
--   Eq. (13) — ℙ(Y ∈ A) = Φ(Φ⁻¹(p_A) − ‖δ‖/σ) for Y ∼ 𝒩(x + δ, σ²I)
-- statement:
--   Let $\sigma>0$, $x,\delta\in\mathbb R^d$ with $\delta\ne0$, and $0<\underline{p_A}<1$. Let $Y\sim\mathcal N(x+\delta,\sigma^2I)$ and let $A$ be the half-space $\{z:\delta^T(z-x)\le\sigma\|\delta\|\Phi^{-1}(\underline{p_A})\}$. Then
--   $$\mathbb P(Y\in A)=\Phi\Big(\Phi^{-1}(\underline{p_A})-\frac{\|\delta\|}{\sigma}\Big).$$
--
--   Shifting the Gaussian by $\delta$ moves mass out of $A$ at a rate governed only by $\|\delta\|/\sigma$.
--
--   **Formalization Note.** $\delta\ne0$ and $0<\underline{p_A}<1$ are added.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A, eq. (13), p. 14; proved as the Claim in Appendix A.0.1, p. 16

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, Appendix A, (13), p. 14 (proved as the
Claim `ℙ(Y ∈ A) = Φ(Φ⁻¹(p̲A) − ‖δ‖/σ)`, Appendix A.0.1, p. 16): for `Y ∼ 𝒩(x + δ, σ²I)`,
`ℙ(Y ∈ A) = Φ(Φ⁻¹(p̲A) − ‖δ‖/σ)`.

**Formalization Note.** `δ ≠ 0` and `0 < p̲A < 1` are added, as for `prob_X_mem_A`. -/
theorem prob_Y_mem_A {d : ℕ} (x δ : Space d) (σ pA : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise (x + δ) σ (setA x δ σ pA)).toReal = Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal pA - ‖δ‖ / σ) := by sorry

end Cohen2019.Tight
