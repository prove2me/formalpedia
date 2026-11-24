-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_G1_isFrame_of
-- name    : Formalism.L2.Geo.Def.G1.isFrame_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:44.820107+00:00
-- url     : https://prove2.me/theorems/c27a4c6f-4653-4ffa-b78b-182bc78d65dd
-- title:
--   G1: is Frame of
-- statement:
--   The G1 construction uses the is Frame of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/DualFrame.lean#L128-L136

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

theorem Formalism.L2.Geo.Def.G1.isFrame_of {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K)
    (h : ∀ z : Fin n → K, z = ∑ i, Formalism.DivisionValues.hform H (w i) z • g i) : IsFrame H g w := by sorry
