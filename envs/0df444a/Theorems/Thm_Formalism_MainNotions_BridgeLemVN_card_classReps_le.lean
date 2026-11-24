-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVN_card_classReps_le
-- name    : Formalism.MainNotions.BridgeLemVN.card_classReps_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:54.782938+00:00
-- url     : https://prove2.me/theorems/a3459c20-31ce-4daa-8e15-b5a3a0b83ce2
-- title:
--   Bridge Lem VN: card class Reps le
-- statement:
--   The Bridge Lem VN construction uses the card class Reps le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L41-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L41-L115

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVN.card_classReps_le (hK : IsCMUnram K) (h : K →ₗ⋆[K] K →ₗ[K] K) (h1 : h 1 1 ≠ 0)
    (s : Finset (Submodule (𝓞 K) K)) (hs : IsClassReps h (1 : Submodule (𝓞 K) K) s) :
    s.card ≤ classNumber K * 2 ^ fDeg K := by sorry
