-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_entry_commute_transposed_R_matrix
-- name    : Formalism.FourierDecayAlt.P.Wd6.entry_commute_transposed_R_matrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:01.040951+00:00
-- url     : https://prove2.me/theorems/d1fe74c1-701f-4aca-890a-dc3766a4872e
-- title:
--   Wd6: entry commute transposed R matrix
-- statement:
--   The Wd6 construction uses the entry commute transposed R matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L157-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L157-L161

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

theorem Formalism.FourierDecayAlt.P.Wd6.entry_commute_transposed_R_matrix {z : SlopeTestRemainingChoices S A} {a : S} (h : ∀ i j, Commute z (eU a i j)) (D : K) : EC z (Rht0 a D) := by sorry
