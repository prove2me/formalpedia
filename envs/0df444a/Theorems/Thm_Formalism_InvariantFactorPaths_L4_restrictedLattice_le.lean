-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_le
-- name    : Formalism.InvariantFactorPaths.L4.restrictedLattice_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:52.396021+00:00
-- url     : https://prove2.me/theorems/2cf9e430-a227-4615-bdeb-20a58fe29e90
-- title:
--   L4: restricted Lattice le
-- statement:
--   The L4 construction uses the restricted Lattice le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L21-L30

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictedLatticeDividedPower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K : ℕ}
variable {r : ℕ} [NeZero r]

theorem Formalism.InvariantFactorPaths.L4.restrictedLattice_le (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (S : Submodule ℤ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))
    (hS : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      initPart (Fin.last K, ρ) 0 h ∈ S) : M2 p LL J M ρ ≤ S := by sorry
