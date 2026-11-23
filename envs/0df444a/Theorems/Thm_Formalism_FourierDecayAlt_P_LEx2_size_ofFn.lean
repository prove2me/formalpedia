-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_size_ofFn
-- name    : Formalism.FourierDecayAlt.P.LEx2.size_ofFn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:37.937986+00:00
-- url     : https://prove2.me/theorems/5f25f0ab-c33e-4f06-8eec-4f8ada8e5717
-- title:
--   LEx2: size of Fn
-- statement:
--   The LEx2 construction uses the size of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L259-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DegreeOfProdLinearLe.lean#L259-L263

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

theorem Formalism.FourierDecayAlt.P.LEx2.size_ofFn (S : Sys) (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ) :
    S.size (List.ofFn fun a => (sg a, Y a)) = ∏ a, |S.P (Y a)| := by sorry
