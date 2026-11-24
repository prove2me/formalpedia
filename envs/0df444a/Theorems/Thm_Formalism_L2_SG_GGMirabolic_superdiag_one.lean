-- Prove2me | Theorems.Thm_Formalism_L2_SG_GGMirabolic_superdiag_one
-- name    : Formalism.L2.SG.GGMirabolic.superdiag_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.252372+00:00
-- url     : https://prove2.me/theorems/464438e6-21ac-4725-bb16-899cebae2f2b
-- title:
--   GGMirabolic: superdiag one
-- statement:
--   The GGMirabolic construction uses the superdiag one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolic.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolic.lean#L43-L49

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
variable {F : Type} [Field F] [Fintype F] (k : ℕ)
variable {k}

theorem Formalism.L2.SG.GGMirabolic.superdiag_one : superdiag k (1 : Matrix (Fin k) (Fin k) F) = 0 := by sorry
