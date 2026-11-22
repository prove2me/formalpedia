-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_keep
-- name    : Formalism.InvariantFactorPaths.L4.ycondC_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:44:20.961838+00:00
-- url     : https://prove2.me/theorems/e92c339a-e872-44d6-b4c5-2af582410569
-- title:
--   L4: ycond C keep
-- statement:
--   The L4 construction uses the ycond C keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L346-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L346-L359

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

theorem Formalism.InvariantFactorPaths.L4.ycondC_keep [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (Mt : WithTop ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      Q x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCondC p LL j Cs Mt, Q x ∈ YCondC p LL j Cs Mt := by sorry
