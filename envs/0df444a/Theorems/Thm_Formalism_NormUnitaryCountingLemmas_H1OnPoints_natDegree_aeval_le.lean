-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_natDegree_aeval_le
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.natDegree_aeval_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:30.940555+00:00
-- url     : https://prove2.me/theorems/288d8286-f83e-4019-8e6d-964bb472f315
-- title:
--   H1 On Points: nat Degree aeval le
-- statement:
--   The H1 On Points construction uses the nat Degree aeval le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L90-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L90-L105

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

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.natDegree_aeval_le {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    (F : MvPolynomial (Fin (N + 1) × Fin n) R) (hF : IsWeightedHomogeneous (blockWt (N + 1) n) F ν)
    (y : Fin (N + 1) × Fin n → Polynomial B)
    (hy : ∀ p, (y p).natDegree ≤ if p.1 = 0 then 1 else 0) : (aeval y F).natDegree ≤ ν 0 := by sorry
