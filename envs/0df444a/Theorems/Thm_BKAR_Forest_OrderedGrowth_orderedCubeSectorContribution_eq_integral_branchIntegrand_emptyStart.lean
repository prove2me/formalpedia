-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
-- name    : BKAR.Forest.OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:00:28.106329+00:00
-- url     : https://prove2.me/theorems/b7f0e36d-d99c-5227-804b-6df5ab32a2a0
-- title:
--   Ordered Growth: ordered Cube Sector Contribution eq integral branch Integrand empty Start
-- statement:
--   An empty-start ordered-growth sector can be read directly as a finite ordered
--   simplex integral of the branch integrand carried by the growth certificate.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L31-L48
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean#L31-L48

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {G : Forest V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.orderedCubeSectorContribution_eq_integral_branchIntegrand_emptyStart
    (growth : OrderedGrowth (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    G.orderedCubeSectorContribution order ρ =
      ∫ ts in orderedFinSimplex order.length,
        growth.branchIntegrand emptyParam ρ (List.ofFn ts) := by sorry
