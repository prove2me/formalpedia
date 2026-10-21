-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_lemma4_low_regret_period
-- name    : CtxInvOpt.Pointed.lemma4_low_regret_period
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:43.297616+00:00
-- url     : https://prove2.me/theorems/eb0efd7d-2cb7-4fa2-b571-18cc875b5e0e
-- title:
--   Lemma 4, p. 20 — if C(I_t) ⊆ E(W_t, U_t) and the test (12) holds, the period's regret is at most ε
-- statement:
--   Let $d=m+1$, $\epsilon>0$, let $C_0\subseteq S^d$ and $c^\star\in C_0$, and let the expert actions $x^\star_s\in\psi(c^\star,\mathcal X_s,f_s)$ be optimal for $c^\star$. Fix a period $t$ with $\mathcal X_t\in\mathfrak B$ and $f_t\in\mathfrak F$, a positive definite diagonal $W_t$ and an orthonormal $U_t$ such that
--   $$C(\mathcal I_t)\subseteq E(W_t,U_t).$$
--   Let the policy play $x^\pi_t\in\psi(U_te_1,\mathcal X_t,f_t)$, let $\delta^\pi_t$ be the effective difference and $\bar\delta=U_t^{-1}\delta^\pi_t$. If (12) holds, $\bar\delta_{[2:d]}'W_t\bar\delta_{[2:d]}\le\epsilon^2$, then the one-period regret is at most $\epsilon$:
--   $$\big(f_t(x^\pi_t)-f_t(x^\star_t)\big)'c^\star\le\epsilon.$$
--
--   Periods that pass the test are therefore cheap, and EllipsoidalCones does not spend a cone update on them.
--
--   **Formalization Note** Lean period $t$ is the paper's $t+1$, and `knowledgeSet C0 X f xstar t` is the paper's $C(\mathcal I_{t+1})$. The paper's parameter $\epsilon>0$ is a hypothesis (for $\epsilon<0$ the test can hold while the regret is $0>\epsilon$).
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 20, Lemma 4; proof App-12–App-13

import Mathlib
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Pointed_EllCone

namespace CtxInvOpt.Pointed

open Matrix

/-- **Lemma 4, p. 20.** Let `C(I_t) ⊆ E(W_t, U_t)` (Lean period `t`, the paper's `t + 1`), where the
knowledge set is built from `C₀ ⊆ S^d` and expert actions optimal for `c⋆ ∈ C₀`. If the policy plays
`x^π_t ∈ ψ(U_t e₁, X_t, f_t)` and the test (12) `δ̄′_{[2:d]} W_t δ̄_{[2:d]} ≤ ε²` holds for
`δ̄ = U_t⁻¹δ^π_t`, then the one-period regret `(f_t(x^π_t) − f_t(x⋆_t))′c⋆` is at most `ε`. -/
theorem lemma4_low_regret_period {n m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hC0 : C0 ⊆ CtxInvOpt.Offline.unitSphere (m + 1))
    (cstar : EuclideanSpace ℝ (Fin (m + 1))) (hcstar : cstar ∈ C0)
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n))
    (hxstar : ∀ s, xstar s ∈ CtxInvOpt.Offline.argminSet cstar (X s) (f s))
    (t : ℕ) (hX : CtxInvOpt.Offline.IsActionSet (X t)) (hf : CtxInvOpt.Offline.IsContext (f t))
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (hK : CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t ⊆ ellCone w U)
    (xpi : EuclideanSpace ℝ (Fin n)) (hxpi : xpi ∈ CtxInvOpt.Offline.argminSet (axisVec U) (X t) (f t))
    (h12 : tailQuad w (rotCoord U (effDiff (f t xpi - f t (xstar t)))) ≤ ε ^ 2) :
    inner ℝ (f t xpi - f t (xstar t)) cstar ≤ ε := by sorry

end CtxInvOpt.Pointed
