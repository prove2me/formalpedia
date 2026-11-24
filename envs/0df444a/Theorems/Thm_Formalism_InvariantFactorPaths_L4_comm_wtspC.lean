-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_comm_wtspC
-- name    : Formalism.InvariantFactorPaths.L4.comm_wtspC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:13.128246+00:00
-- url     : https://prove2.me/theorems/e4664234-2912-43c7-9e8d-664c2b32146b
-- title:
--   L4: comm wtsp C
-- statement:
--   The L4 construction uses the comm wtsp C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L22-L33

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.comm_wtspC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ x, Q (glAct p LL j c c x) = glAct p LL j c c (Q x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j Cs μ, Q x ∈ WtSpC p LL j Cs μ := by sorry
