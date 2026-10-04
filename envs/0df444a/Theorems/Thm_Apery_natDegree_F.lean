-- Prove2me | Theorems.Thm_Apery_natDegree_F
-- name    : Apery.natDegree_F
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-01T10:52:42.361616+00:00
-- url     : https://prove2.me/theorems/7fa90752-fa30-462c-b684-00d97de6c115
-- title:
--   Degree of the normalized Hankel polynomial
-- statement:
--   For every natural number $n$, the rational polynomial $F_n$ from the Hankel construction satisfies
--   $$\operatorname{natDegree}(F_n)=37n.$$
--   This includes $n=0$. It supplies the exact degree required by the final integer-polynomial estimate.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Degree.lean#L177-L178

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem natDegree_F (n : ℕ) : (F n).natDegree = 37 * n := by sorry

end Apery
