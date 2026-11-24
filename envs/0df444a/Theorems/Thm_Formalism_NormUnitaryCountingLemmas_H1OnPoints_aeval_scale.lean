-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_aeval_scale
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.aeval_scale
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:45.920714+00:00
-- url     : https://prove2.me/theorems/5053dc71-8c42-41f9-9491-02726c08502f
-- title:
--   H1 On Points: aeval scale
-- statement:
--   The H1 On Points construction uses the aeval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L19-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L19-L38

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

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.aeval_scale {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    (F : MvPolynomial (Fin N × Fin n) R)
    (hF : IsWeightedHomogeneous (blockWt N n) F ν) (lam : Fin N → S) (y : Fin N × Fin n → S) :
    aeval (fun p => lam p.1 * y p) F = (∏ j, lam j ^ ν j) * aeval y F := by sorry
