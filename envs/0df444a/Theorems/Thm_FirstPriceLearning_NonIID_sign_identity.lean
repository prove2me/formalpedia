-- Prove2me | Theorems.Thm_FirstPriceLearning_NonIID_sign_identity
-- name    : FirstPriceLearning.NonIID.sign_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:33:00.991989+00:00
-- url     : https://prove2.me/theorems/024f6d90-4436-45b5-a40a-9a4388aa4363
-- title:
--   Proof of Theorem 8, p. 34 — $\mathrm{sign}(v_t-v^\star)=-\mathrm{sign}(u_t)$
-- statement:
--   Let $u\in\{\pm1\}^T$, let $v^\star=f(u)=\frac12+\frac14\sum_{s=1}^T u_s/2^s$, and let $v_1=\frac12$, $v_{t+1}=v_t+u_t/2^{t+2}$. Then for every round $t\in[T]$,
--   $$
--   \operatorname{sign}(v_t-v^\star)=\operatorname{sign}\!\left(\frac12+\frac14\sum_{s=1}^{t-1}\frac{u_s}{2^s}-\Big(\frac12+\frac14\sum_{s=1}^{T}\frac{u_s}{2^s}\Big)\right)=-\operatorname{sign}(u_t).
--   $$
--   In particular $v_t\neq v^\star$, and $v_t\ge v^\star$ exactly when $u_t=-1$. With $m_t\equiv0$ under $P$ and $m_t\equiv1/8$ under $Q$, this gives $m_t=\frac18\mathbb 1(u_t=-1)$: the HOB at round $t$ is decided by a sign the bidder has not seen.
--
--   **Formalization Note** $\operatorname{sign}$ is Mathlib's `SignType.sign`. The sum $\sum_{s=1}^{t-1}$ ranges over the Lean rounds $s<t$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8, definition of (v_t) and the sign display

import Mathlib
import Definitions.Def_FirstPriceLearning_NonIID_HardInstance

namespace FirstPriceLearning.NonIID

/-- Proof of Theorem 8, arXiv:2003.09795v7, p. 34 (the `sign` display): for `u ∈ {±1}^T`,
`v⋆ = f(u)` and the values `v_1 = 1/2`, `v_{t+1} = v_t + u_t / 2^{t+2}`,
`sign(v_t − v⋆) = sign(1/2 + (1/4)∑_{s<t} u_s/2^s − (1/2 + (1/4)∑_{s≤T} u_s/2^s)) = −sign(u_t)`. -/
theorem sign_identity (T : ℕ) (u : Fin T → ℝ) (hu : ∀ s, u s = 1 ∨ u s = -1) (t : Fin T) :
    SignType.sign (valueSeq u t - fval u) =
        SignType.sign ((1 / 2 + 1 / 4 * ∑ s ∈ Finset.univ.filter (fun s : Fin T => s < t),
            u s / 2 ^ (s.val + 1)) -
          (1 / 2 + 1 / 4 * ∑ s : Fin T, u s / 2 ^ (s.val + 1))) ∧
      SignType.sign ((1 / 2 + 1 / 4 * ∑ s ∈ Finset.univ.filter (fun s : Fin T => s < t),
            u s / 2 ^ (s.val + 1)) -
          (1 / 2 + 1 / 4 * ∑ s : Fin T, u s / 2 ^ (s.val + 1))) = -SignType.sign (u t) := by sorry

end FirstPriceLearning.NonIID
