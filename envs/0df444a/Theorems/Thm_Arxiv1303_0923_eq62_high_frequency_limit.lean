-- Prove2me | Theorems.Thm_Arxiv1303_0923_eq62_high_frequency_limit
-- name    : Arxiv1303_0923.eq62_high_frequency_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:31:06.064559+00:00
-- url     : https://prove2.me/theorems/869d55fe-7b94-44e1-83db-699e4db34b3d
-- title:
--   Eq. (62) (with corrected constant): the high-frequency limit of $4ik(u/u_0-1)$ is $2\int_{L(x,x_0)}q\,ds$
-- statement:
--   Assume the standing setting of Section 1: bounded domains $\Omega\subset G_1\subset G$ in $\mathbb{R}^3$, $G_1$ convex with $C^1$ boundary $S$, and $\varepsilon\in(0,1)$ with $\operatorname{dist}(S,\partial G)>2\varepsilon$, $\operatorname{dist}(S,\partial\Omega)>2\varepsilon$. Let $q$ satisfy (3), (4) with $m=2$, and for every source $x_0\in\mathbb{R}^3$ and every real $k$ let $u(\cdot,x_0,k)$ be the solution of (5)-(7) of the form (8), (9). Then for all $x,x_0\in\mathbb{R}^3$ with $x\neq x_0$,
--   $$\lim_{k\to+\infty}4ik\Big(\frac{u(x,x_0,k)}{u_0(x,x_0,k)}-1\Big)=2\int_{L(x,x_0)}q(\xi)\,ds .$$
--
--   This high-frequency limit turns equality of the complex fields on $S$ into equality of the line integrals of $q_1$ and $q_2$ over all chords of $S$ (eq. (63)), which the Radon transform then inverts.
--
--   **Formalization Note** The paper's (62) has the limit $\int_{L(x,x_0)}q\,ds$ without the factor $2$. It inherits a factor-$2$ error from (27) and (35): for a constant potential $q\equiv c$ the exact field $e^{i\sqrt{k^2-c}\,r}/(4\pi r)$ gives the limit $2cr=2\int_Lq\,ds$. The statement uses the corrected value. The factor cancels in (63), so the uniqueness theorems are unaffected. The limit is taken along real $k\to+\infty$.
-- source:
--   M. V. Klibanov, Phaseless inverse scattering problems in 3-d, arXiv:1303.0923v1 (2013), claim c010; Section 3.3, eq. (62), PDF p. 13

import Mathlib
import Definitions.Def_Arxiv1303_0923_Basic

open MeasureTheory Filter Topology

namespace Arxiv1303_0923

theorem eq62_high_frequency_limit (geo : Geometry) (q : R3 → ℝ)
    (hq : IsPotential geo.G 2 q) (u : R3 → R3 → ℝ → ℂ)
    (hu : ∀ (x0 : R3) (k : ℝ), IsPointSourceSolution 2 q x0 k (fun x => u x x0 k))
    (x x0 : R3) (hxx0 : x ≠ x0) :
    Tendsto (fun k : ℝ => 4 * Complex.I * k * (u x x0 k / incWave x x0 k - 1)) atTop
      (𝓝 ((2 * segInt q x x0 : ℝ) : ℂ)) := by sorry

end Arxiv1303_0923
