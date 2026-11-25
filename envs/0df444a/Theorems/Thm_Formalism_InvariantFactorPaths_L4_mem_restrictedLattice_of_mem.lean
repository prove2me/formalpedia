-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_restrictedLattice_of_mem
-- name    : Formalism.InvariantFactorPaths.L4.mem_restrictedLattice_of_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:22:12.715874+00:00
-- url     : https://prove2.me/theorems/eab0a3c9-042d-4f0d-9c9b-96cce85a002e
-- title:
--   L4: mem restricted Lattice of mem
-- statement:
--   The L4 construction uses the mem restricted Lattice of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L15-L19

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

theorem Formalism.InvariantFactorPaths.L4.mem_restrictedLattice_of_mem (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (o : ℕ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hY : h ∈ Y p (setLast LL o) J M)
    (hi : h ∈ IntPol p (Fin (K + 1) × Fin r)) : initPart (Fin.last K, ρ) 0 h ∈ M2 p LL J M ρ := by sorry
