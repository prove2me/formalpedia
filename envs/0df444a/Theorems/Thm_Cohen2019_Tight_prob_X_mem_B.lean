-- Prove2me | Theorems.Thm_Cohen2019_Tight_prob_X_mem_B
-- name    : Cohen2019.Tight.prob_X_mem_B
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:30:24.047812+00:00
-- url     : https://prove2.me/theorems/edbd2afc-fafb-426a-b85c-7829dc75ec6b
-- title:
--   Appendix A.0.1, Claim — ℙ(X ∈ B) = p_B for X ∼ 𝒩(x, σ²I)
-- statement:
--   Let $\sigma>0$, $x\in\mathbb R^d$, $\delta\in\mathbb R^d$ with $\delta\ne0$, and $0<\overline{p_B}<1$. Let $X\sim\mathcal N(x,\sigma^2I)$ and $B=\{z:\delta^T(z-x)\ge\sigma\|\delta\|\Phi^{-1}(1-\overline{p_B})\}$. Then
--   $$\mathbb P(X\in B)=\overline{p_B}.$$
--
--   The half-space $B$ is calibrated so that the worst-case classifier puts exactly the allowed mass $\overline{p_B}$ on the runner-up class $c_B$.
--
--   **Formalization Note.** $\delta\ne0$ and $0<\overline{p_B}<1$ are added. The paper's proof recalls $B$ with "$\le$" and writes $\mathbb P(X\in A)$ in its first line; both are misprints, and $B$ is the set defined on p. 14.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A.0.1, Claim ℙ(X ∈ B) = p_B, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, Appendix A.0.1, Claim `ℙ(X ∈ B) = p̄B`, p. 15:
for `X ∼ 𝒩(x, σ²I)`, the half-space `B = {z : δᵀ(z − x) ≥ σ‖δ‖Φ⁻¹(1 − p̄B)}` has probability
`p̄B`. (The proof on p. 15 recalls `B` with `≤` and writes `ℙ(X ∈ A)` in its first line; both
are misprints, and `B` is the set defined on p. 14.)

**Formalization Note.** The hypotheses `δ ≠ 0` and `0 < p̄B < 1` are added, as for
`prob_X_mem_A`. -/
theorem prob_X_mem_B {d : ℕ} (x δ : Space d) (σ pB : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpB0 : 0 < pB) (hpB1 : pB < 1) :
    (gaussNoise x σ (setB x δ σ pB)).toReal = pB := by sorry

end Cohen2019.Tight
