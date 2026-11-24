-- Prove2me | Theorems.Thm_Formalism_L2_SG_LsDatumA_lemma0L_holds
-- name    : Formalism.L2.SG.LsDatumA.lemma0L_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:07.071951+00:00
-- url     : https://prove2.me/theorems/a2f40b5e-7f7a-42a9-9934-a0f724180583
-- title:
--   Ls Datum A: lemma0 L holds
-- statement:
--   The Ls Datum A construction uses the lemma0 L holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LsDatumA.lean#L50-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LsDatumA.lean#L50-L106

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.LsDatumA
open Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Formalism.L2.SG.LsDatumA.lemma0L_holds (M : Model F E) (r : ℕ) : Lemma0L M r := by sorry
