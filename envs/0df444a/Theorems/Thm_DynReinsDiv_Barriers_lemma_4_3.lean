-- Prove2me | Theorems.Thm_DynReinsDiv_Barriers_lemma_4_3
-- name    : DynReinsDiv.Barriers.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:09.896603+00:00
-- url     : https://prove2.me/theorems/71fa2b7f-9062-4490-965f-a1f3e64ad997
-- title:
--   Lemma 4.3 — v_x, v_t ∈ C^{2,1} in 𝒩𝒟, v_xx < 0 in 𝒩𝒟, and Î(z, x, τ) = max{z + v_x/v_xx, 0}
-- statement:
--   Let $v$ be the solution of Theorem 3.1 (with $0<\gamma<\mu_1$), in the variables $(x,\tau)$, and let $\mathcal{ND}=\{(x,\tau): x>0,\ 0<\tau\le T,\ v_x(x,\tau)>1\}$ be the no-dividend region. Then:
--   1. on $\mathcal{ND}$ the functions $v_x$ and $v_t$ are of class $C^{2,1}$: the derivatives $\partial_x v_{xx}$, $\partial_\tau v_x$, $\partial_x v_t$, $\partial_{xx} v_t$ and $\partial_\tau v_t$ exist there (the $\tau$-derivatives one-sided at $\tau=T$), and $v_x$, $v_{xx}$, $v_t$ and these derivatives are continuous on $\mathcal{ND}$;
--   2. $v_{xx}<0$ on $\mathcal{ND}$;
--   3. for every $z>0$ and $(x,\tau)\in\mathcal{ND}$,
--   $$\hat I(z,x,\tau)=\max\Bigl\{z+\frac{v_x}{v_{xx}}(x,\tau),\ 0\Bigr\}.$$
--
--   The strict concavity in item 2 makes the optimal ceded loss an explicit, nondecreasing function of the claim size inside the no-dividend region; the regularity in item 1 is what the implicit function theorem needs for the reinsurance boundaries.
--
--   **Formalization Note** The regularity is stated with explicit derivative functions: `HasDerivAt` on $x$-sections and `HasDerivWithinAt` on $\tau$-sections within $[0,T]$, at every point of $\mathcal{ND}$, $0<\tau\le T$. The edge $\tau=T$ is the paper's $t=0$, which belongs to $\mathcal{ND}\subseteq\mathcal Q^T=(0,\infty)\times[0,T)$.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 15, Lemma 4.3, (4.7)

import Mathlib
import Definitions.Def_DynReinsDiv_Barriers_Model
import Definitions.Def_DynReinsDiv_Barriers_Boundaries

namespace DynReinsDiv.Barriers

/-- Lemma 4.3 (arXiv:2008.00391v3, p. 15). For the solution `v` of Theorem 3.1 (second argument
`τ`):
1. `v_x, v_t ∈ C^{2,1}(𝒩𝒟)` on `𝒩𝒟 = {x > 0, 0 < τ ≤ T, v_x > 1}` (the edge `τ = T`, i.e. the
   paper's `t = 0`, included): there are functions `vxxx = ∂_x v_xx`, `vxt = ∂_τ v_x`,
   `vtx = ∂_x v_t`, `vtxx = ∂_x vtx`, `vtt = ∂_τ v_t` there (the `τ`-derivatives taken within
   `[0, T]`, so one-sided at `τ = T`), and `v_x, v_xx, vxxx, vxt, v_t, vtx, vtxx, vtt` are
   continuous on `𝒩𝒟`;
2. `v_xx < 0` on `𝒩𝒟 = {x > 0, 0 < τ ≤ T, v_x > 1}`;
3. `Î(z, x, τ) = max{z + v_x/v_xx(x, τ), 0}` for `z > 0` and `(x, τ) ∈ 𝒩𝒟`. -/
theorem lemma_4_3 (M : Model) (v vx vxx vt : ℝ → ℝ → ℝ)
    (hv : M.IsTheorem31Solution v vx vxx vt) :
    (∃ vxxx vxt vtx vtxx vtt : ℝ → ℝ → ℝ,
      ContinuousOn (Function.uncurry vx) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vxx) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vxxx) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vxt) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vt) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vtx) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vtxx) (NDset M.T vx) ∧
      ContinuousOn (Function.uncurry vtt) (NDset M.T vx) ∧
      ∀ p ∈ NDset M.T vx,
        HasDerivAt (fun y => vxx y p.2) (vxxx p.1 p.2) p.1 ∧
        HasDerivWithinAt (fun s => vx p.1 s) (vxt p.1 p.2) (Set.Icc 0 M.T) p.2 ∧
        HasDerivAt (fun y => vt y p.2) (vtx p.1 p.2) p.1 ∧
        HasDerivAt (fun y => vtx y p.2) (vtxx p.1 p.2) p.1 ∧
        HasDerivWithinAt (fun s => vt p.1 s) (vtt p.1 p.2) (Set.Icc 0 M.T) p.2) ∧
    (∀ p ∈ NDset M.T vx, vxx p.1 p.2 < 0) ∧
    (∀ z : ℝ, 0 < z → ∀ p ∈ NDset M.T vx,
      Ihat vx vxx z p.1 p.2 = max (z + vx p.1 p.2 / vxx p.1 p.2) 0) := by sorry

end DynReinsDiv.Barriers
