-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_G1_hform_eq
-- name    : Formalism.L2.Geo.Def.G1.hform_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:20.672413+00:00
-- url     : https://prove2.me/theorems/f29779e6-f8d7-4958-b1cf-fc9fcdd1db81
-- title:
--   G1: hform eq
-- statement:
--   The G1 construction uses the hform eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L120-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L120-L123

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {K : Type} [Field K] [StarRing K]

theorem Formalism.L2.Geo.Def.G1.hform_eq {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = Formalism.UG.hform (starRingEnd K) H x y := by sorry
