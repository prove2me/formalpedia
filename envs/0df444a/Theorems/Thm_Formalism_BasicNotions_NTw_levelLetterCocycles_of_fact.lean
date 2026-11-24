-- Prove2me | Theorems.Thm_Formalism_BasicNotions_NTw_levelLetterCocycles_of_fact
-- name    : Formalism.BasicNotions.NTw.levelLetterCocycles_of_fact
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:34:22.96309+00:00
-- url     : https://prove2.me/theorems/1f6fc467-9695-4753-81e9-62ce737546eb
-- title:
--   NTw: level Letter Cocycles of fact
-- statement:
--   The NTw construction uses the level Letter Cocycles of fact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean#L468-L468
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean#L468-L468

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
attribute [instance] NData.instOm NData.algOm NData.acOm NData.lPrime NData.instO NData.domO
  NData.dvrO NData.algO NData.finO NData.topO NData.trO NData.finX NData.neX NData.acgMt
  NData.modMt NData.freeMt NData.finMt NData.acgBj NData.modBj NData.freeBj NData.finBj
  NData.finPlG
attribute [instance] NTw.lPrime NTw.topO0 NTw.twistBaseCoefficientRing_topologicalRing NTw.topO NTw.trO NTw.crO0 NTw.twistBaseCoefficientRing_isDomain NTw.twistBaseCoefficientRing_isDVR NTw.algO0 NTw.twistBaseCoefficientRing_finite_padic NTw.crO NTw.domO
  NTw.dvrO NTw.algO NTw.crOk NTw.domOk NTw.dvrOk NTw.algOk NTw.finSig NTw.acgB NTw.modB
  NTw.freeB NTw.finB NTw.finLam NTw.grpRCG NTw.finRCG
open Formalism.BasicNotions.NTw
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (X : NTw R H what₂ LL0 N)

theorem Formalism.BasicNotions.NTw.levelLetterCocycles_of_fact (h : X.TwCover) : X.CoverAtSplitPlaces := by sorry
