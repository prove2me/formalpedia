-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pow_intertwine
-- name    : Formalism.InvariantFactorPaths.L4.pow_intertwine
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:53:42.821604+00:00
-- url     : https://prove2.me/theorems/6a2afbef-9c89-47f5-91df-724d44948318
-- title:
--   L4: pow intertwine
-- statement:
--   The L4 construction uses the pow intertwine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictedLatticeDividedPower.lean#L46-L50

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

theorem Formalism.InvariantFactorPaths.L4.pow_intertwine {V : Type} [AddCommGroup V] [Module ℚ_[p] V] (R A B : V →ₗ[ℚ_[p]] V)
    (h : ∀ x, R (A x) = B (R x)) (k : ℕ) (x : V) : R ((A ^ k) x) = (B ^ k) (R x) := by sorry
