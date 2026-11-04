-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_clarke_singleton_strict
-- name    : ChanceStateCtrl.PDE.clarke_singleton_strict
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T12:39:15.395421+00:00
-- url     : https://prove2.me/theorems/a10153fb-75fb-4ef9-a24d-928965e389ed
-- title:
--   Clarke, Prop. 2.2.4 — a singleton Clarke subdifferential gives strict differentiability (Hilbert space)
-- statement:
--   Let $H$ be a real Hilbert space, with its dual identified with $H$ through the inner product, and let $f:H\to\mathbb R$ be locally Lipschitzian around $u\in H$. Clarke's directional derivative is
--   $$f^\circ(u;h)=\limsup_{u'\to u,\ t\downarrow0}\frac{f(u'+th)-f(u')}{t},$$
--   and the Clarke subdifferential is $\partial^Cf(u)=\{y\in H\mid (y,h)\le f^\circ(u;h)\ \forall h\in H\}$.
--
--   If $\partial^Cf(u)=\{y\}$ is a singleton, then $f$ is strictly (Hadamard) differentiable at $u$ with derivative $y$: for every $h\in H$,
--   $$\lim_{u'\to u,\ t\downarrow0}\frac{f(u'+th)-f(u')}{t}=(y,h).$$
--
--   This is the step of Theorem 2.2 (p. 5) of the source paper that turns the singleton conclusion under (16) into strict differentiability of the probability function ("$\varphi$ is strictly differentiable at $\bar u$ in the Hadamard sense [10, p. 30]"); it is used for Corollary 2.11.
--
--   **Formalization Note.** The limit is taken along the filter $\mathcal N(u)\times\mathcal N_{>0}(0)$ on $H\times\mathbb R$, matching the definition of `clarkeDir`.
-- source:
--   F. Clarke, Optimization and Nonsmooth Analysis, Wiley 1983, Proposition 2.2.4 (p. 33; strict differentiability, p. 30); used in Geiersbach & Henrion, arXiv:2306.03965v2, p. 5, Theorem 2.2 and p. 10, Corollary 2.11

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Clarke (1983), Proposition 2.2.4, on a real Hilbert space `H` (with `H*` identified with `H`):
if `f` is locally Lipschitzian around `u` and `∂^C f(u) = {y}`, then `f` is strictly (Hadamard)
differentiable at `u` with derivative `y`: for every direction `h`,
`(f(u' + t h) - f(u')) / t → (y, h)` as `u' → u`, `t ↓ 0`. -/
theorem clarke_singleton_strict {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (u y : H) (hf : LocLipschitzAt f u)
    (hy : clarkeSubdiffL2 f u = {y}) (h : H) :
    Tendsto (fun q : H × ℝ => (f (q.1 + q.2 • h) - f q.1) / q.2) (𝓝 u ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (inner ℝ y h)) := by sorry

end ChanceStateCtrl.PDE
