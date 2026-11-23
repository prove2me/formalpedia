-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_blockSum
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.blockSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:42.106793+00:00
-- url     : https://prove2.me/theorems/612f3cdf-7008-4d61-83c9-5b34ada20e87
-- title:
--   H1 On Points: block Sum
-- statement:
--   The H1 On Points construction uses the block Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L11-L17

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NatDegreeAevalLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.H1OnPoints
variable {R : Type*} [CommRing R]

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.blockSum {N n : ℕ} {ν : Fin N → ℕ} (d : Fin N × Fin n →₀ ℕ)
    (hd : Finsupp.weight (blockWt N n) d = ν) (j : Fin N) : ∑ k, d (j, k) = ν j := by sorry
