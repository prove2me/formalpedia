-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_inv
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:33.682807+00:00
-- url     : https://prove2.me/theorems/ea75a6d0-0946-45ed-9c3e-d936c7664f45
-- title:
--   H1 On Points: shear inv
-- statement:
--   The H1 On Points construction uses the shear inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L61-L66

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

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_inv {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν) (i j : Fin N) (hij : i < j)
    (y : Fin N × Fin n → S) (s : S) :
    aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) F = aeval y F := by sorry
