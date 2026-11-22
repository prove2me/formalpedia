-- Prove2me | Theorems.Thm_Erdos462RH_twoScale_of_selberg
-- name    : Erdos462RH.twoScale_of_selberg
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:07:02.367235+00:00
-- url     : https://prove2.me/theorems/9eda3b84-8d4f-405b-b392-b538ef201d00
-- title:
--   Specialization to the two factor scales
-- statement:
--   Assume the explicit relative Selberg estimate. For each real $N\ge 9797\cdot10^{15}$, write $d=512(\log N)^2/N$. At each of $Y=2N$ and $Y=2N/3$ one has $J_\theta(Y,d)\le 3dY^2(\log N)^2$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Section 2, equation (2).

import Definitions.Def_Erdos462Selberg

namespace Erdos462RH
theorem twoScale_of_selberg (hS : SelbergBound) : TwoScaleBound := by sorry
end Erdos462RH
