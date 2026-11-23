-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Ts_star
-- name    : Formalism.FourierDecayAlt.P.Wd6.Ts_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:45.541634+00:00
-- url     : https://prove2.me/theorems/c6762b28-5d06-41af-ad42-b9123cbdca50
-- title:
--   Wd6: Ts star
-- statement:
--   The Wd6 construction uses the Ts star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L363-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L363-L366

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
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.Ts_star (σ : Site A) {Y : K} (hY : star Y = Y) :
    (Ts σ Y).map star = Tm Y (star σ.p) (star σ.c) (star σ.ci) := by sorry
