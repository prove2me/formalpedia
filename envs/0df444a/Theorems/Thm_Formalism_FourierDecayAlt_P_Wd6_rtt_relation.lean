-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_rtt_relation
-- name    : Formalism.FourierDecayAlt.P.Wd6.rtt_relation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:53.373305+00:00
-- url     : https://prove2.me/theorems/7d4e70d1-9cce-49bd-baf1-067c8735daba
-- title:
--   Wd6: rtt relation
-- statement:
--   The Wd6 construction uses the rtt relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L244-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L244-L247

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

theorem Formalism.FourierDecayAlt.P.Wd6.rtt_relation (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    Rh0 a D * lift0 M * d0 (ins a (lift0 N)) = d0 (ins a (lift0 N)) * lift0 M * Rh0 a D := by sorry
