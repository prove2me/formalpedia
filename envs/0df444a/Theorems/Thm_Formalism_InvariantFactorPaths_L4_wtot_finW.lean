-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtot_finW
-- name    : Formalism.InvariantFactorPaths.L4.wtot_finW
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:03:17.075049+00:00
-- url     : https://prove2.me/theorems/9d9e8ea3-2a5b-58f9-9fa7-8951461a263d
-- title:
--   L4: wtot fin W
-- statement:
--   The L4 construction uses the wtot fin W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L316-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L316-L338

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
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
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)

theorem Formalism.InvariantFactorPaths.L4.wtot_finW (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ))
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    G.FinW (Wtot p LL J M (Fin.last s)) := by sorry
