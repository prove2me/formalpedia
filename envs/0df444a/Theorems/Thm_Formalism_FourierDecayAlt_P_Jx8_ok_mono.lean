-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_ok_mono
-- name    : Formalism.FourierDecayAlt.P.Jx8.ok_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:30.026912+00:00
-- url     : https://prove2.me/theorems/0edd9329-47b5-4b2f-8a66-c642716c40cc
-- title:
--   Jx8: ok mono
-- statement:
--   The Jx8 construction uses the ok mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L269-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OutsideSystemsBound.lean#L269-L274

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8

theorem Formalism.FourierDecayAlt.P.Jx8.ok_mono {E α : Type} [Field E] {S : LocSys E α} {F G : Finset α} (h : F ⊆ G) (hS : S.Ok G) :
    S.Ok F := by sorry
