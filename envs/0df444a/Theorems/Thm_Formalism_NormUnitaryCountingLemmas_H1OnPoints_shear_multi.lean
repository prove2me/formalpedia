-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_H1OnPoints_shear_multi
-- name    : Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_multi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:30.781351+00:00
-- url     : https://prove2.me/theorems/c050b52b-aab6-4294-afbf-4e5cab63bc32
-- title:
--   H1 On Points: shear multi
-- statement:
--   The H1 On Points construction uses the shear multi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L68-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NatDegreeAevalLe.lean#L68-L88

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

theorem Formalism.NormUnitaryCountingLemmas.H1OnPoints.shear_multi {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (y : Fin (N + 1) × Fin n → S) (s : Fin (N + 1) → S) (T : Finset (Fin (N + 1)))
    (hT : (0 : Fin (N + 1)) ∉ T) :
    aeval (fun p => y p + if p.1 ∈ T then s p.1 * y (0, p.2) else 0) F = aeval y F := by sorry
