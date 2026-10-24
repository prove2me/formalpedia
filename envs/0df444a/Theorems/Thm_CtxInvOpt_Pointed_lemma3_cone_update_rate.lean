-- Prove2me | Theorems.Thm_CtxInvOpt_Pointed_lemma3_cone_update_rate
-- name    : CtxInvOpt.Pointed.lemma3_cone_update_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:23.762418+00:00
-- url     : https://prove2.me/theorems/76bbef4e-a295-4a31-bc14-d99c20bd2ffd
-- title:
--   Lemma 3, p. 18 — C(I_{t+1}) ⊆ E(W_t,U_t) ∩ {δ′c ≥ 0} ⊆ E(W_{t+1},U_{t+1}); for d ≥ 3, ∏λ_i shrinks by e^{−1/(d−1)}
-- statement:
--   Let $d=m+1\ge 2$. In period $t$, let $W_t$ be positive definite diagonal and $U_t$ orthonormal with
--   $$C(\mathcal I_t)\subseteq E(W_t,U_t),$$
--   let the policy play $x^\pi_t\in\psi(U_te_1,\mathcal X_t,f_t)$, let $x^\star_t\in\psi(c^\star,\mathcal X_t,f_t)$, and let $\delta^\pi_t$ be the effective difference, with $(U_t^{-1}\delta^\pi_t)_{[2:d]}\ne0$. If $(W_{t+1},U_{t+1})$ is any output of ConeUpdate on $(W_t,U_t,\delta^\pi_t)$ with $\eta=0$, $B=I_d$, $p=d$, then
--   $$C(\mathcal I_{t+1})\subseteq E(W_t,U_t)\cap\{c\in\mathbb R^d:\ \delta^{\pi\,\prime}_tc\ge0\}\subseteq E(W_{t+1},U_{t+1})$$
--   and
--   if moreover $d\ge3$,
--   $$\prod_{i=1}^{d-1}\lambda_i(W_{t+1})\le e^{-1/(d-1)}\prod_{i=1}^{d-1}\lambda_i(W_t).$$
--
--   The cone therefore keeps containing every cost consistent with the observations, while its "volume" falls geometrically with each update.
--
--   **Formalization Note** The rate is stated for $d\ge3$ only, and the two inclusions for every $d\ge2$: at $d=2$ ConeUpdate's $p=2$ branch sets $\widetilde W=W/2$, and $1/2>e^{-1}=e^{-1/(d-1)}$, so the printed rate fails there while the inclusions hold. For $d\ge3$ the product equals $\det N=\big(\tfrac{m^2}{m^2-1}\big)^m\tfrac{m-1}{m+1}\det W\le e^{-1/m}\det W$. The rate does not follow from Lemma B-1, which only gives $e^{-1/(2(d-1))}$. The hypothesis $(U_t^{-1}\delta^\pi_t)_{[2:d]}\ne0$ holds in every cone-update period (otherwise the left side of (12) is $0$). Lean period $t$ is the paper's $t+1$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 18, Lemma 3; proof App-11

import Mathlib
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate

namespace CtxInvOpt.Pointed

open Matrix

/-- **Lemma 3, p. 18 (`d = m + 1 ≥ 2`; the rate for `d ≥ 3`).** Run ConeUpdate with inputs `W_t = diag(w)`, `U_t = U`,
`δ^π_t`, `η = 0`, `B = I_d`, `p = d`, where `x^π_t ∈ ψ(U e₁, X_t, f_t)` and `x⋆_t ∈ ψ(c⋆, X_t, f_t)`.
If `C(I_t) ⊆ E(W_t, U_t)`, then
`C(I_{t+1}) ⊆ E(W_t, U_t) ∩ {c : δ^π_t′c ≥ 0} ⊆ E(W_{t+1}, U_{t+1})` and
`∏ λ_i(W_{t+1}) ≤ e^{−1/(d−1)} ∏ λ_i(W_t)` when `d ≥ 3` (at `d = 2` ConeUpdate halves `W`, and
`1/2 > e^{−1}`, so the printed rate fails there). Lean period `t` is the paper's `t + 1`. -/
theorem lemma3_cone_update_rate {n m : ℕ} (hm : 1 ≤ m)
    (C0 : Set (EuclideanSpace ℝ (Fin (m + 1)))) (cstar : EuclideanSpace ℝ (Fin (m + 1)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ)
    (hxstar : xstar t ∈ CtxInvOpt.Offline.argminSet cstar (X t) (f t))
    (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (hU : U ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ)
    (hK : CtxInvOpt.Greedy.knowledgeSet C0 X f xstar t ⊆ ellCone w U)
    (xpi : EuclideanSpace ℝ (Fin n)) (hxpi : xpi ∈ CtxInvOpt.Offline.argminSet (axisVec U) (X t) (f t))
    (htail : tailVec (rotCoord U (effDiff (f t xpi - f t (xstar t)))) ≠ 0)
    (w' : Fin m → ℝ) (U' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hupd : IsConeUpdate w U (effDiff (f t xpi - f t (xstar t))) w' U') :
    CtxInvOpt.Greedy.knowledgeSet C0 X f xstar (t + 1) ⊆
        ellCone w U ∩ {c | 0 ≤ inner ℝ (effDiff (f t xpi - f t (xstar t))) c} ∧
      ellCone w U ∩ {c | 0 ≤ inner ℝ (effDiff (f t xpi - f t (xstar t))) c} ⊆ ellCone w' U' ∧
      (2 ≤ m → ∏ i, w' i ≤ Real.exp (-(1 / (m : ℝ))) * ∏ i, w i) := by sorry

end CtxInvOpt.Pointed
