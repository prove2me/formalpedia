-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_xsp
-- name    : Formalism.InvariantFactorPaths.L4.mem_xsp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:39:12.056194+00:00
-- url     : https://prove2.me/theorems/a30b5b95-9cb7-4e6f-a5e3-d026e90ea3b8
-- title:
--   L4: mem xsp
-- statement:
--   The L4 construction uses the mem xsp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKeepsSpaceHolds.lean#L12-L23

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.mem_xsp [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    x ∈ XSp p LL J M ρ ↔ x ∈ Pol p r LL ∧ x ∈ FreeOf p (Fin.last K, ρ) ∧
      ∀ k, (K + 1 ≤ J k → x ∈ YCond p LL K (M k) ∧ x ∈ TypesLE p LL (K + 1) (univ.erase ρ) (M k)) ∧
        (¬ K + 1 ≤ J k → x ∈ YCond p LL (J k) (M k)) := by sorry
