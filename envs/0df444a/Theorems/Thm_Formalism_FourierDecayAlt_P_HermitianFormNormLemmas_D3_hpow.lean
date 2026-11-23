-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormNormLemmas_D3_hpow
-- name    : Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:22.454795+00:00
-- url     : https://prove2.me/theorems/b2f27837-c2bc-489b-97dc-caeb14de51d4
-- title:
--   D3: hpow
-- statement:
--   The D3 construction uses the hpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L730-L739
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentBlockMeasure.lean#L730-L739

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical

theorem Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hpow {b x c : ℝ} (hb : 1 < b) (hx0 : 0 ≤ x) (hx : x ≤ b ^ c) (n : ℕ) {K M : ℝ}
    (h : c * n ≤ K * M) : x ^ n ≤ Real.exp (K * M * Real.log b) := by sorry
