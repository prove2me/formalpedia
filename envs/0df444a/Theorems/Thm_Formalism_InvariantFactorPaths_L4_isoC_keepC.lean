-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_isoC_keepC
-- name    : Formalism.InvariantFactorPaths.L4.isoC_keepC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:49.696426+00:00
-- url     : https://prove2.me/theorems/77c4d7a3-21f8-42d2-837e-09987d8eb31c
-- title:
--   L4: iso C keep C
-- statement:
--   The L4 construction uses the iso C keep C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L60-L72

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

theorem Formalism.InvariantFactorPaths.L4.isoC_keepC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hQ : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x)) :
    ∀ x ∈ IsoC p LL j Cs la, Q x ∈ IsoC p LL j Cs la := by sorry
