-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_unit_mul
-- name    : Formalism.FourierDecayAlt.P.Wd6.unit_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:58.554516+00:00
-- url     : https://prove2.me/theorems/a024e445-17d1-49ad-a8d4-c87fb47100ea
-- title:
--   Wd6: unit mul
-- statement:
--   The Wd6 construction uses the unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L177-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L177-L183

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.unit_mul (a : S) (i j r s : Fin 2) (x y : A) :
    ((eU a i j : SlopeTestRemainingChoices S A) * io x) * (eU a r s * io y) = if j = r then eU a i s * io (x * y) else 0 := by sorry
