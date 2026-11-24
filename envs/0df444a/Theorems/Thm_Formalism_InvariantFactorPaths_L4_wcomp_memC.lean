-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wcomp_memC
-- name    : Formalism.InvariantFactorPaths.L4.wcomp_memC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:45.815093+00:00
-- url     : https://prove2.me/theorems/ea691978-a01a-44f5-8d5c-e1b73f5a4e66
-- title:
--   L4: wcomp mem C
-- statement:
--   The L4 construction uses the wcomp mem C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L197-L200

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

theorem Formalism.InvariantFactorPaths.L4.wcomp_memC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ c ∈ Cs, ∀ x ∈ S, glAct p LL j c c x ∈ S) (μ : Fin r → ℤ) :
    ∀ x ∈ S, compP (fun m => ∀ c ∈ Cs, wt LL j c m = μ c) x ∈ S := by sorry
