-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_mid_levPos
-- name    : Formalism.FourierDecayAlt.P.B2x2.mid_levPos
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:43:50.595018+00:00
-- url     : https://prove2.me/theorems/f45e293c-99a8-4467-a820-51630bb7e0cd
-- title:
--   B2x2: mid lev Pos
-- statement:
--   The B2x2 construction uses the mid lev Pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L258-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L258-L261

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2

theorem Formalism.FourierDecayAlt.P.B2x2.mid_levPos (k r' : ℕ) (s : Fin (2 * r' + k + 1)) : mid k r' (levPos k 1 r' s) := by sorry
