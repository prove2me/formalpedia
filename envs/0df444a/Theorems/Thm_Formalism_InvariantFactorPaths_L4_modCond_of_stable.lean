-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_modCond_of_stable
-- name    : Formalism.InvariantFactorPaths.L4.modCond_of_stable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:37.707061+00:00
-- url     : https://prove2.me/theorems/f509755e-8669-4d2d-9469-3439c462082a
-- title:
--   L4: mod Cond of stable
-- statement:
--   The L4 construction uses the mod Cond of stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L135-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L135-L146

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)
variable (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.modCond_of_stable (S : Set (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, ∀ c : Fin r, c ≠ 0 → ∀ k, dpow p LL j c k x ∈ S)
    (hs : ∀ x ∈ S, ∀ m : Fin N × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) → ‖coeff m x‖ < 1) :
    ∀ x ∈ S, ModCond p LL j M x := by sorry
