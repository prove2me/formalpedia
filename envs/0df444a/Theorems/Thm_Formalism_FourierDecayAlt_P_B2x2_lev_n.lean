-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_n
-- name    : Formalism.FourierDecayAlt.P.B2x2.lev_n
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:41:02.32293+00:00
-- url     : https://prove2.me/theorems/13a8ae84-2c23-41dd-972b-8d23c86ca8a3
-- title:
--   B2x2: lev n
-- statement:
--   The B2x2 construction uses the lev n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CompactGroupHaarExists.lean#L291-L295

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

theorem Formalism.FourierDecayAlt.P.B2x2.lev_n (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : ¬ mid k r' p) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by sorry
