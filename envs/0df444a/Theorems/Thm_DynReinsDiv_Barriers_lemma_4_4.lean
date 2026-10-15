-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_lemma_4_4
-- name    : DynReinsDiv.Barriers.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:12.784049+00:00
-- url     : https://prove2.me/theorems/57d05374-15ee-4ec0-a2bf-f85a0e5e6dc0
-- title:
--   Lemma 4.4 — (−v_x/v_xx)|_{x=0} = 1/λ, −v_x/v_xx > 1/λ and ∂_x(−v_x/v_xx) ≥ 2c in 𝒩𝒟
-- statement:
--   Let $v$ be the solution of Theorem 3.1 (with $0<\gamma<\mu_1$), in the variables $(x,\tau)$, and let $\lambda>0$ be a root of $f(y)=-yA(y)+B(y)-\gamma$ (A.12). Let $\mathcal{ND}=\{(x,\tau): x>0,\ 0<\tau\le T,\ v_x(x,\tau)>1\}$. Then
--   $$\Bigl(-\frac{v_x}{v_{xx}}\Bigr)\Big|_{x=0}=\frac1\lambda\quad(0<\tau\le T), \tag{4.8}$$
--   $$-\frac{v_x}{v_{xx}}(x,\tau)>\frac1\lambda\quad\text{for }(x,\tau)\in\mathcal{ND}, \tag{4.9}$$
--   and at every $(x,\tau)\in\mathcal{ND}$ the function $y\mapsto -v_x(y,\tau)/v_{xx}(y,\tau)$ is differentiable at $x$ with
--   $$\partial_x\Bigl(-\frac{v_x}{v_{xx}}\Bigr)(x,\tau)\ge 2c. \tag{4.10}$$
--
--   The quantity $-v_x/v_{xx}$ is the optimal retention level; the lemma says it starts at $1/\lambda$ on the ruin boundary and grows at rate at least $2c$ in the surplus.
--
--   **Formalization Note** In (4.8), $v_x(0,\tau)$ and $v_{xx}(0,\tau)$ are the continuous extensions of the derivatives to $x=0$. (4.10) asserts the existence of the derivative as well as the bound.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 15, Lemma 4.4, (4.8)–(4.10)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries

namespace DynReinsDiv.Barriers

/-- Lemma 4.4 (arXiv:2008.00391v3, p. 15). Let `v` be the solution of Theorem 3.1 (second argument
`τ`) and `λ > 0` a root of `f` (A.12). Then
(4.8) `−v_x/v_xx = 1/λ` at `x = 0`, for `0 < τ ≤ T` (boundary values of `v_x`, `v_xx`);
(4.9) `−v_x/v_xx(x, τ) > 1/λ` on `𝒩𝒟 = {x > 0, 0 < τ ≤ T, v_x > 1}`;
(4.10) on `𝒩𝒟`, `x ↦ −v_x/v_xx(x, τ)` is differentiable with derivative
`≥ 2c`. -/
theorem lemma_4_4 (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0) :
    (∀ τ : ℝ, 0 < τ → τ ≤ M.T → -vx 0 τ / vxx 0 τ = 1 / lam) ∧
    (∀ p ∈ NDset M.T vx, -vx p.1 p.2 / vxx p.1 p.2 > 1 / lam) ∧
    (∀ p ∈ NDset M.T vx, ∃ g : ℝ,
      HasDerivAt (fun y => -vx y p.2 / vxx y p.2) g p.1 ∧ 2 * M.c ≤ g) := by sorry

end DynReinsDiv.Barriers
