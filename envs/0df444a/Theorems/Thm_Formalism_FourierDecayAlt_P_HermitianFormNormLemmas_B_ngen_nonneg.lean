-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_B_ngen_nonneg
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.ngen_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:54.259689+00:00
-- url     : https://prove2.me/theorems/02d51196-0450-4c59-87cd-b268904e4bf1
-- title:
--   B: ngen nonneg
-- statement:
--   The B construction uses the ngen nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L270-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L270-L285

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
variable {Cl Nu : Type}

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.B.ngen_nonneg (L : LocalNG Cl Nu) (C0 r : ℕ) (hb : L.Basic) (hM : L.MassRatioAt C0 r) (p : L.P) :
    0 ≤ L.ngen p := by sorry
