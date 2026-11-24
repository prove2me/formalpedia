-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diagScalar_commute_of_entries
-- name    : Formalism.FourierDecayAlt.P.Wd6.diagScalar_commute_of_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:52.748508+00:00
-- url     : https://prove2.me/theorems/f7402929-5777-4fac-97c8-788e797e79e2
-- title:
--   Wd6: diag Scalar commute of entries
-- statement:
--   The Wd6 construction uses the diag Scalar commute of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L283-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L283-L284

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

theorem Formalism.FourierDecayAlt.P.Wd6.diagScalar_commute_of_entries {z : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : EC z M) : d0 z * M = M * d0 z := by sorry
