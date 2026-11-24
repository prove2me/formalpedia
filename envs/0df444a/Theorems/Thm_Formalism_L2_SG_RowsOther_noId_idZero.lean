-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_noId_idZero
-- name    : Formalism.L2.SG.RowsOther.noId_idZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:44.2758+00:00
-- url     : https://prove2.me/theorems/d75b937a-1ad2-4f0d-93e8-c8502d045f90
-- title:
--   Rows Other: no Id id Zero
-- statement:
--   The Rows Other construction uses the no Id id Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L58-L61

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

theorem Formalism.L2.SG.RowsOther.noId_idZero : (noId X).IdZero := by sorry
