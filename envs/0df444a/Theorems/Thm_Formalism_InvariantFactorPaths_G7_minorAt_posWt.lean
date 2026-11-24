-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_minorAt_posWt
-- name    : Formalism.InvariantFactorPaths.G7.minorAt_posWt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:12.119798+00:00
-- url     : https://prove2.me/theorems/e465db72-3fd2-423f-b289-fbc204784641
-- title:
--   G7: minor At pos Wt
-- statement:
--   The G7 construction uses the minor At pos Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L329-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L329-L347

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.minorAt_posWt {l : ℕ} (s s' : σ) (T : Fin l → Fin r0 → K) (I : Fin l → Fin r1) :
    MvPolynomial.IsWeightedHomogeneous (posWt r0 r1 s) (minorAt s' T I)
      (if s' = s then l else 0) := by sorry
