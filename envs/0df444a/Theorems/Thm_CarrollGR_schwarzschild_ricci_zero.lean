-- Prove2me | Theorems.Thm_CarrollGR_schwarzschild_ricci_zero
-- name    : CarrollGR.schwarzschild_ricci_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-26T00:14:59.163239+00:00
-- url     : https://prove2.me/theorems/c25df3a0-956e-44b4-b01e-22ff1e51d2b5
-- title:
--   The Schwarzschild metric solves the vacuum Einstein equation
-- statement:
--   Let $G>0$ and $m>0$. The Schwarzschild metric
--
--   $$ds^2=-\left(1-\frac{2Gm}{r}\right)dt^2+\left(1-\frac{2Gm}{r}\right)^{-1}dr^2+r^2(d\theta^2+\sin^2\theta\,d\phi^2)$$
--
--   has vanishing Ricci tensor, $R_{\mu\nu}=0$, at every point $(t,r,\theta,\phi)$ with $r>0$, $r\neq2Gm$ and $0<\theta<\pi$ — both outside ($r>2Gm$) and inside ($0<r<2Gm$) the event horizon.
--
--   This is the existence half of Carroll's statement that (72) is *the* solution of the vacuum equation (69) with spherical symmetry.
--
--   **Formalization Note** The points $r=0$, $r=2Gm$ where the components blow up, and $\sin\theta=0$ where the coordinates degenerate, are excluded.
-- source:
--   S. M. Carroll, "A No-Nonsense Introduction to General Relativity" (lecture notes, 2001), uploaded PDF, p. 17, eq. (72) (with eq. (69), p. 16)

import Mathlib
import Definitions.Def_CarrollGR_Defs

open scoped ContDiff

namespace CarrollGR

theorem schwarzschild_ricci_zero (GN m : ℝ) (hGN : 0 < GN) (hm : 0 < m) (x : Coord)
    (hr : 0 < x 1) (hr' : x 1 ≠ 2 * GN * m) (hθ : x 2 ∈ Set.Ioo 0 Real.pi) (μ ν : Fin 4) :
    ricci (schwarzschild GN m) μ ν x = 0 := by sorry

end CarrollGR
