-- Prove2me | Theorems.Thm_BKAR_Forest_orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
-- name    : BKAR.Forest.orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:38.27672+00:00
-- url     : https://prove2.me/theorems/4edec28d-3c53-46c7-8bbc-511e9ba2a1b0
-- title:
--   Forest: ordered Contribution eq ordered Simplex Integral order Measurable Equiv symm
-- statement:
--   Recursive ordered contributions, rewritten with the same finite coordinates
--   used on the cube-sector side.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L537-L550
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean#L537-L550

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.orderedContribution_eq_orderedSimplexIntegral_orderMeasurableEquiv_symm
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedContribution order ρ =
      orderedSimplexIntegral order
        (fun ts =>
          mixedPartialList order.reverse ρ
            (F.standardInterp
              ((F.orderMeasurableEquivOfOrder horder).symm
                (fun i : Fin order.length => ts.getD i.val 0)))) := by sorry
