-- Prove2me | Theorems.Thm_CalibratedCE_Generic_example_CE_not_limit
-- name    : CalibratedCE.Generic.example_CE_not_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:10:39.816237+00:00
-- url     : https://prove2.me/theorems/951efcb2-f9d3-4b48-bf52-4f95c125d537
-- title:
--   Example (p. 48) — in a non-generic $3\times3$ game a correlated equilibrium is not a limit of calibrated play
-- statement:
--   In the $3\times3$ game of p. 48 (Row's strategies $A,B,C$, Column's $1,2,3$; payoffs Row\Col: $A$: 2\2, 0\3, 0\1; $B$: 2\2, 0\1, 0\3; $C$: 2\0, 1\1, 1\0), let $D_0$ put probability $1/2$ on $(A,1)$ and $1/2$ on $(B,1)$. Then $D_0$ is a correlated equilibrium but not a limit point of calibrated forecasts:
--   $$D_0 \in \pi(G),\qquad D_0 \notin \lambda(G),$$
--   so $\pi(G) \ne \lambda(G)$.
--
--   The reason given on the page is that $M_b(A) = M_b(B) = \{(1,0,0)\}$, so a stationary best-reply function of Row plays at most one of $A$ and $B$. This example shows that "almost every" cannot be dropped from Theorem 2. The game is non-generic: its payoffs satisfy linear equalities (rows $A$ and $B$ of Row's payoffs coincide), a set of games of Lebesgue measure zero.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 48, example after the proof of Theorem 2

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet
import Definitions.Def_CalibratedCE_Generic_Example

namespace CalibratedCE.Generic

theorem example_CE_not_limit :
    exD₀ ∈ CESet exU₁ exU₂ ∧ exD₀ ∉ LimitSet exU₁ exU₂ := by sorry

end CalibratedCE.Generic
