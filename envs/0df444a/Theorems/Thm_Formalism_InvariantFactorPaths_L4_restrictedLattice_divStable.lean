-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_restrictedLattice_divStable
-- name    : Formalism.InvariantFactorPaths.L4.restrictedLattice_divStable
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:55:52.675638+00:00
-- url     : https://prove2.me/theorems/fca7c739-0ff5-4a5d-8bc7-3863dde9832f
-- title:
--   L4: restricted Lattice div Stable
-- statement:
--   The L4 construction uses the restricted Lattice div Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L346-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L346-L397

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
variable {s : ℕ}

theorem Formalism.InvariantFactorPaths.L4.restrictedLattice_divStable (hU : UDivInt) (hD : DWDivInt) (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c) :
    DivStable G.E (M2 p LL J M (Fin.last s)).toAddSubgroup := by sorry
