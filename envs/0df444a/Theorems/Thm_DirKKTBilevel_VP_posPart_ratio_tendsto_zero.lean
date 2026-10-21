-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_posPart_ratio_tendsto_zero
-- name    : DirKKTBilevel.VP.posPart_ratio_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:28.055621+00:00
-- url     : https://prove2.me/theorems/06230f5e-5efa-4c39-8b03-acf279895040
-- title:
--   Proof of Theorem 3.1, p. 10 — for u ∈ C(z̄), ‖ϕ₊(z̄ + tu)‖/t → 0 as t ↓ 0
-- statement:
--   Let $X$ be a real inner product space, $\varphi:X\to\mathbb R$ and $\phi:X\to\mathbb R^q$. Let $\bar z$ satisfy $\phi(\bar z)\le0$, suppose $\phi$ has directional derivative $\phi'(\bar z;u)$ at $\bar z$ in direction $u$, and suppose $u\in C(\bar z)$, that is, $\phi_j'(\bar z;u)\le0$ for every active index $j$ and $\nabla\varphi(\bar z)u\le0$. Then, with $\phi_+$ the componentwise positive part and $\|\cdot\|$ the Euclidean norm,
--   $$\lim_{t\downarrow0}\frac{\|\phi_+(\bar z+tu)\|}{t}=0.$$
--
--   Along a critical direction the constraint violation is of higher order than the step; this is the first step of the proof of Theorem 3.1.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 10, proof of Theorem 3.1

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Proof of Theorem 3.1, p. 10: if `z` is feasible for `con ≤ 0`, `con` has directional
derivative `d = ϕ'(z; u)` at `z` in direction `u`, and `u ∈ C(z)`, then
`lim_{t↓0} ‖ϕ₊(z + tu)‖ / t = 0`. -/
theorem posPart_ratio_tendsto_zero {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) :
    Tendsto (fun t : ℝ => ‖posPart (con (z + t • u))‖ / t) (𝓝[>] 0) (𝓝 0) := by sorry

end DirKKTBilevel.VP
