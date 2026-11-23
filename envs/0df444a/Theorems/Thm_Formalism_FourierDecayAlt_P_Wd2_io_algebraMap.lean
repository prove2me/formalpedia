-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_io_algebraMap
-- name    : Formalism.FourierDecayAlt.P.Wd2.io_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:15.287702+00:00
-- url     : https://prove2.me/theorems/d5270530-f1c3-499c-a356-a6a40357a47e
-- title:
--   Wd2: io algebra Map
-- statement:
--   The Wd2 construction uses the io algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L233-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L233-L236

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd2.io_algebraMap (c : K) : (io (algebraMap K A c) : SlopeTestRemainingChoices S A) = algebraMap K (SlopeTestRemainingChoices S A) c := by sorry
