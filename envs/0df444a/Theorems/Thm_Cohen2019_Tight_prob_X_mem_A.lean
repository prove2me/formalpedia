-- Prove2me | Theorems.Thm_Cohen2019_Tight_prob_X_mem_A
-- name    : Cohen2019.Tight.prob_X_mem_A
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:30:27.373884+00:00
-- url     : https://prove2.me/theorems/9d2ea776-dec6-404a-ac9d-0081f3119cff
-- title:
--   Appendix A.0.1, Claim — ℙ(X ∈ A) = p_A for X ∼ 𝒩(x, σ²I)
-- statement:
--   Let $\sigma>0$, $x\in\mathbb R^d$, $\delta\in\mathbb R^d$ with $\delta\ne0$, and $0<\underline{p_A}<1$. Let $X\sim\mathcal N(x,\sigma^2I)$ and $A=\{z:\delta^T(z-x)\le\sigma\|\delta\|\Phi^{-1}(\underline{p_A})\}$. Then
--   $$\mathbb P(X\in A)=\underline{p_A}.$$
--
--   The half-space $A$ is calibrated so that the worst-case classifier puts exactly the allowed mass $\underline{p_A}$ on $c_A$.
--
--   **Formalization Note.** $\delta\ne0$ and $0<\underline{p_A}<1$ are added: at $\delta=0$ the set $A$ is all of $\mathbb R^d$, and $\Phi^{-1}$ is finite only on $(0,1)$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, Appendix A.0.1, Claim ℙ(X ∈ A) = p_A, p. 15

import Mathlib
import Definitions.Def_Cohen2019_Tight_Model
import Definitions.Def_Cohen2019_Tight_HalfSpaces

open MeasureTheory ProbabilityTheory

namespace Cohen2019.Tight

/-- Cohen, Rosenfeld, Kolter, arXiv:1902.02918v2, Appendix A.0.1, Claim `ℙ(X ∈ A) = p̲A`, p. 15:
for `X ∼ 𝒩(x, σ²I)`, the half-space `A = {z : δᵀ(z − x) ≤ σ‖δ‖Φ⁻¹(p̲A)}` has probability `p̲A`.

**Formalization Note.** The hypotheses `δ ≠ 0` and `0 < p̲A < 1` are added: the computation
divides by `‖δ‖` (at `δ = 0`, `A` is all of `ℝᵈ`), and uses `Φ(Φ⁻¹(p)) = p`, which needs
`Φ⁻¹(p)` finite. -/
theorem prob_X_mem_A {d : ℕ} (x δ : Space d) (σ pA : ℝ) (hσ : 0 < σ) (hδ : δ ≠ 0)
    (hpA0 : 0 < pA) (hpA1 : pA < 1) :
    (gaussNoise x σ (setA x δ σ pA)).toReal = pA := by sorry

end Cohen2019.Tight
