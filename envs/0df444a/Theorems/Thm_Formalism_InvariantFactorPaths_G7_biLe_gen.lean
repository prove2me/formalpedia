-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_gen
-- name    : Formalism.InvariantFactorPaths.G7.biLe_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:16.095098+00:00
-- url     : https://prove2.me/theorems/1e7ea028-f564-45e9-bbcd-290fb0dc632c
-- title:
--   G7: bi Le gen
-- statement:
--   The G7 construction uses the bi Le gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L241-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L241-L245

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
variable {K ι κ : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.biLe_gen [Fintype κ] (b : κ → ι → K) (x : ι) : BiLe (Finsupp.single x 1)
    (MvPolynomial.C (MvPolynomial.X x) +
      ∑ k, MvPolynomial.C (MvPolynomial.C (b k x)) * MvPolynomial.X k :
        MvPolynomial κ (MvPolynomial ι K)) := by sorry
