-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_KerPTh_of
-- name    : Formalism.L2.Th1.H.KerPTh_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:33.96507+00:00
-- url     : https://prove2.me/theorems/dc609768-f5be-4942-b920-d64a752d7918
-- title:
--   H: Ker PTh of
-- statement:
--   The H construction uses the Ker PTh of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L241-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/ExtensionInterSubspace.lean#L241-L284

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_ExtensionInterSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.KerPTh_of (hE : ExpSeriesEntire) (hS : LatGaussSummable) (hN : FormNorm) : KerPTh := by sorry
