-- Prove2me | Theorems.Thm_AllPhotonicRepeater_twoLevel_closed_forms
-- name    : AllPhotonicRepeater.twoLevel_closed_forms
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:22:11.173987+00:00
-- url     : https://prove2.me/theorems/66eb882a-9fdd-4084-93db-0a061534048d
-- title:
--   Eqs. (A1), (A3), (A13), (A16): closed forms for a two-level tree
-- statement:
--   For a two-level tree ($l=1$, branching $b_0,b_1$, as in Fig. 4 of the paper) and every loss probability $\epsilon_0$,
--   $$
--   R_1=1-\epsilon_0^{\,b_1},\qquad P_X=R_0=1-\big(1-(1-\epsilon_0)^{b_1+1}\big)^{b_0},
--   $$
--   $$
--   P_Z=\big(1-\epsilon_0^{\,b_1+1}\big)^{b_0},\qquad Q_L=b_0+b_0b_1 .
--   $$
--   These closed forms are what one gets from (A3) with $R_2=R_3=0$ and $b_2=0$, and make the dependence of $P_Z$, $P_X$ and $Q_L$ on the branching explicit. They are the starting point for choosing a tree with small failure probability.
--
--   Differences from the source:
--   - reading: (A3) printed for $1\le k\le l$ → $R_k$ given by (A3) also at $k=0$; reason: (A16) reads $P_X=R_0$, and (A7), (A9), (A12) give $R_k=1-(1-S_k)^{b_k}$ at every level, $k=0$ included
--   - encoding: $R_{l+1}:=0$ and $b_{l+1}:=0$ → $R_k=0$ and $b_k$ read as $0$ for every $k>l$; reason: $R_{l+2}$ enters only $R_l$, raised to the power $b_{l+1}=0$, so its value never matters; same instances
--   - generalization: $\epsilon_0$ a loss probability with $\epsilon_0<0.5$ → every real $\epsilon_0$; reason: the identities are polynomial identities; they specialize to the paper's range
--   - reading: general depth $l$ in (A1), (A3), (A13), (A16) → the case $l=1$ evaluated in closed form; reason: the paper states the general recursion; this item evaluates it at the depth of Fig. 4, which the scaling argument can use
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A1, Eqs. (A1), (A3), p. 7; App. A2, Eqs. (A13), (A16), p. 9; Fig. 4, p. 7

import Mathlib
import Definitions.Def_AllPhotonicRepeater_treeSize
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, Eqs. (A1), (A3),
p. 7, and (A13), (A16), p. 9, for a two-level tree (`l = 1`, as in Fig. 4, p. 7): for every
loss probability `ε0` and branching `b 0, b 1`,

* `R_1 = 1 − ε0^{b_1}`,
* `P_X = R_0 = 1 − (1 − (1 − ε0)^{b_1 + 1})^{b_0}`,
* `P_Z = (1 − ε0^{b_1 + 1})^{b_0}`,
* `Q_L = b_0 + b_0 b_1`.

**Formalization Note** These follow from (A3) with `R_2 = R_3 = 0` and `b_2 = 0`. Natural-number
powers with `0 ^ 0 = 1`, which is also the paper's convention. An independent cross-check, not a
dependency: the platform's Open goal
`QAlgorithms.Papers.Independent.Intakenext100.P89.depth_two_measurements` (Pant et al.) has the
same right-hand sides with `p = 1 − ε0`, for an operational loss experiment. -/
theorem twoLevel_closed_forms (ε0 : ℝ) (b : ℕ → ℕ) :
    indirectZSuccess ε0 1 b 1 = 1 - ε0 ^ b 1 ∧
    xSuccess ε0 1 b = 1 - (1 - (1 - ε0) ^ (b 1 + 1)) ^ b 0 ∧
    zSuccess ε0 1 b = (1 - ε0 ^ (b 1 + 1)) ^ b 0 ∧
    treeSize 1 b = b 0 + b 0 * b 1 := by sorry

end AllPhotonicRepeater
