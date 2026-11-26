-- Prove2me | Theorems.Thm_BKAR_Forest_canonicalGrownForestForSupport_cubeContribution_eq_of_choices
-- name    : BKAR.Forest.canonicalGrownForestForSupport_cubeContribution_eq_of_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:03:24.89458+00:00
-- url     : https://prove2.me/theorems/64219b3d-9dc2-5cd8-94c0-d79ac52153ec
-- title:
--   Forest: canonical Grown Forest For Support cube Contribution eq of choices
-- statement:
--   For a fixed support, the canonical grown cube contribution is independent
--   of the auxiliary active-extension choice system.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L165-L172
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean#L165-L172

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.canonicalGrownForestForSupport_cubeContribution_eq_of_choices
    (choices₁ choices₂ : ActiveExtensionChoice V) (I : ForestIndex V)
    (ρ : (Edge V → ℝ) → ℝ) (hρ : BKARContDiff ρ) :
    (canonicalGrownForestForSupport choices₁ I).cubeContribution ρ =
      (canonicalGrownForestForSupport choices₂ I).cubeContribution ρ := by sorry
