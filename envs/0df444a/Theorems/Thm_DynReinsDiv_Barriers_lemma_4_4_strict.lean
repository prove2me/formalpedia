-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_lemma_4_4_strict
-- name    : DynReinsDiv.Barriers.lemma_4_4_strict
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T22:01:06.107349+00:00
-- url     : https://prove2.me/theorems/ec92583f-907c-4867-913d-4eae612c6ed5
-- title:
--   Strict (4.10): $\partial_x(-v_x/v_{xx}) > 2c$ in $\mathcal{ND}$ (used in the proof of Theorem 4.5)
-- statement:
--   Let $v$ be the solution of Theorem 3.1 (with second argument $\tau$ = time to maturity), let $\lambda>0$ be a root of the function $f(y)=-yA(y)+B(y)-\gamma$ of (A.12), and let
--   $$\mathcal{ND}=\{(x,\tau): x>0,\ 0<\tau\le T,\ v_x(x,\tau)>1\}$$
--   be the no-dividend-payout region. Then for every $(x,\tau)\in\mathcal{ND}$ the map $y\mapsto -\dfrac{v_x}{v_{xx}}(y,\tau)$ is differentiable at $x$ and
--   $$\partial_x\Bigl(-\frac{v_x}{v_{xx}}\Bigr)(x,\tau)>2c .$$
--
--   This is the strict form of (4.10) that the paper invokes in the proof of Theorem 4.5 ("Because $\partial_x(-v_x/v_{xx})>2c$ in $\mathcal{ND}$, the implicit function theorem implies ..."). It follows from the inequality (D.1) of Appendix D,
--   $$\nu_x\ \ge\ \frac{1}{A(1/\nu)}\Bigl[f\bigl(1/\nu\bigr)\,\nu+c\,\nu^2\Bigr],\qquad \nu=-\frac{v_x}{v_{xx}},$$
--   together with $\nu>1/\lambda$ in $\mathcal{ND}$ (4.9), the strict decrease of $f$ (so $f(1/\nu)>f(\lambda)=0$), and $0<A(1/\nu)\le \nu^2/2$.
--
--   **Formalization Note** Same hypotheses as the milestone Lemma 4.4 (`DynReinsDiv.Barriers.lemma_4_4`); only the derivative bound is made strict. The derivative is stated as `HasDerivAt` of `y ↦ -v_x(y,τ)/v_xx(y,τ)` at `x`, with the derivative witnesses `vx`, `vxx` of the model.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 20 (proof of Theorem 4.5: '∂x(−vx/vxx) > 2c in ND'), via Appendix D (inequality (D.1) for ν = −vx/vxx, (4.9), f strictly decreasing)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries

namespace DynReinsDiv.Barriers

/-- Strict form of (4.10), used in the proof of Theorem 4.5 (arXiv:2008.00391v3, p. 20:
"Because `∂_x(−v_x/v_xx) > 2c` in `𝒩𝒟`"). Let `v` be the solution of Theorem 3.1 (second
argument `τ`) and `λ > 0` a root of `f` (A.12). On `𝒩𝒟 = {x > 0, 0 < τ ≤ T, v_x > 1}` the map
`x ↦ −v_x/v_xx(x, τ)` is differentiable with derivative strictly greater than `2c`. -/
theorem lemma_4_4_strict (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) (lam : ℝ) (hlam : 0 < lam) (hf : M.fA lam = 0) :
    ∀ p ∈ NDset M.T vx, ∃ g : ℝ,
      HasDerivAt (fun y => -vx y p.2 / vxx y p.2) g p.1 ∧ 2 * M.c < g := by sorry

end DynReinsDiv.Barriers
