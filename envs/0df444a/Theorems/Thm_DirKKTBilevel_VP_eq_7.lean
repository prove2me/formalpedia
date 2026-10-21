-- Prove2me | Theorems.Thm_DirKKTBilevel_VP_eq_7
-- name    : DirKKTBilevel.VP.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:27.544659+00:00
-- url     : https://prove2.me/theorems/5f32b676-3a85-4f16-bb73-0e87b6db5383
-- title:
--   Eq. (7), proof of Theorem 3.1, p. 10 — the penalized objective has zero directional derivative along u ∈ C(z̄)
-- statement:
--   Let $X$ be a real inner product space, $\varphi:X\to\mathbb R$ continuously differentiable at $\bar z$, and $\phi:X\to\mathbb R^q$ with $\phi(\bar z)\le0$. Suppose $\phi$ has directional derivative $\phi'(\bar z;u)$ at $\bar z$ in direction $u\in C(\bar z)$, and that (P) $\min\varphi$ s.t. $\phi\le0$ is calm at $\bar z$ in direction $u$ with constants $\varepsilon,\delta,\rho>0$: $\varphi(z)-\varphi(\bar z)+\rho\|\alpha\|\ge0$ whenever $\|\alpha\|<\varepsilon$, $z\in\bar z+\mathcal V_{\varepsilon,\delta}(u)$ and $\phi(z)+\alpha\le0$. Then
--   $$\lim_{t\downarrow0}\frac{\varphi(\bar z+tu)+\rho\|\phi_+(\bar z+tu)\|-\varphi(\bar z)}{t}=0. \tag{7}$$
--
--   The penalized function $\varphi+\rho\|\phi_+\|$ is therefore flat to first order along $u$; this is used in the proof of Theorem 3.1 to keep the Ekeland points inside the directional neighbourhood.
--
--   **Formalization Note** The modulus $\rho$ is the calmness modulus of Definition 3.1, from which inequality (6) of the paper is derived.
-- source:
--   Bai, Ye, Directional necessary optimality conditions for bilevel programs, arXiv:2004.01783v3, p. 10, proof of Theorem 3.1, eq. (7)

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional

namespace DirKKTBilevel.VP

/-- Eq. (7), proof of Theorem 3.1, p. 10: if `z` is feasible, `obj` is continuously
differentiable at `z`, `con` has directional derivative `d` at `z` in direction `u ∈ C(z)`,
and (P) is calm at `z` in direction `u` with constants `ε, δ, ρ > 0`, then
`lim_{t↓0} (obj(z + tu) + ρ‖ϕ₊(z + tu)‖ − obj(z)) / t = 0`. -/
theorem eq_7 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q) (ε δ ρ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hobj : ContDiffAt ℝ 1 obj z) (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) (hcalm : IsCalmDirWith obj con z u ε δ ρ) :
    Tendsto (fun t : ℝ => (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t)
      (𝓝[>] 0) (𝓝 0) := by sorry

end DirKKTBilevel.VP
