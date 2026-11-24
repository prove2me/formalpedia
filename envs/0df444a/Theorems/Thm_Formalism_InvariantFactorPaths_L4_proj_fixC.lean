-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_proj_fixC
-- name    : Formalism.InvariantFactorPaths.L4.proj_fixC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:32.483983+00:00
-- url     : https://prove2.me/theorems/e1644928-2204-409e-a23c-97b6d56478d5
-- title:
--   L4: proj fix C
-- statement:
--   The L4 construction uses the proj fix C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L283-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L283-L308

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

theorem Formalism.InvariantFactorPaths.L4.proj_fixC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hP : IsTypeProj p LL j Cs T P) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S) (hPS : ∀ x ∈ S, P x ∈ S)
    (hT : ∀ h ∈ S, h ≠ 0 → ∀ μ, h ∈ HWC p LL j Cs μ → μ ∈ T) : ∀ x ∈ S, P x = x := by sorry
