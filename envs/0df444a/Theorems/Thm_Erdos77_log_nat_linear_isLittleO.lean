-- Prove2me | Theorems.Thm_Erdos77_log_nat_linear_isLittleO
-- name    : Erdos77.log_nat_linear_isLittleO
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T14:16:38.84598+00:00
-- url     : https://prove2.me/theorems/f4399949-108d-4684-ba02-0c7c016fd5e6
-- title:
--   Logarithmic correction is sublinear
-- statement:
--   The logarithmic correction log(2k+1) grows sublinearly in k.
-- source:
--   Standard logarithmic growth estimate in real asymptotics.

import Mathlib
open Filter Topology

namespace Erdos77
theorem log_nat_linear_isLittleO :
  (fun k : Nat => Real.log (2 * (k : Real) + 1)) =o[atTop] (fun k : Nat => (k : Real)) := by sorry
end Erdos77
