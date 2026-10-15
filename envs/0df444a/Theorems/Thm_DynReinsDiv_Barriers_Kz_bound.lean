-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_Kz_bound
-- name    : DynReinsDiv.Barriers.Kz_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:13.425268+00:00
-- url     : https://prove2.me/theorems/6d36c577-63ad-4b8a-8d58-1df751b2a9e2
-- title:
--   Section 4.2, p. 18 — for z > 1/λ the reinsurance boundary satisfies K(z, τ) ≤ z/2c − 1/(2cλ)
-- statement:
--   Let $v$ be the solution of Theorem 3.1 (with $0<\gamma<\mu_1$), in the variables $(x,\tau)$, let $\lambda>0$ be a root of $f$ (A.12), and let
--   $$K(z,\tau)=\sup\Bigl\{x>0: -\frac{v_{xx}}{v_x}(x,\tau)>\frac1z\Bigr\}$$
--   be the reinsurance boundary for claims of size $z$ (zero if the set is empty). If $z>1/\lambda$, then for every $\tau\in(0,T]$,
--   $$K(z,\tau)\le\frac{z}{2c}-\frac{1}{2c\lambda}.$$
--
--   A claim of size $z$ is partly reinsured only when the surplus is below $K(z,\tau)$, so the bound gives a horizon-free surplus level above which claims of size $z$ are retained in full.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 18, Section 4.2 (unnumbered; Figure 4 restricts it to z > 1/λ)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries

namespace DynReinsDiv.Barriers

/-- Section 4.2, p. 18 (arXiv:2008.00391v3): for the solution `v` of Theorem 3.1 (second argument
`τ`), a root `λ > 0` of `f` (A.12) and a claim size `z > 1/λ`, the reinsurance boundary satisfies
`K(z, τ) ≤ z/(2c) − 1/(2cλ)` for every `τ ∈ (0, T]`. -/
theorem Kz_bound (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0)
    (z : ℝ) (hz : 1 / lam < z) :
    ∀ τ ∈ Set.Ioc 0 M.T, Kz vx vxx z τ ≤ z / (2 * M.c) - 1 / (2 * M.c * lam) := by sorry

end DynReinsDiv.Barriers
