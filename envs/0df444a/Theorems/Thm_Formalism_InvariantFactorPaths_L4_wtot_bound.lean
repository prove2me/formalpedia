-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtot_bound
-- name    : Formalism.InvariantFactorPaths.L4.wtot_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:55:51.638194+00:00
-- url     : https://prove2.me/theorems/71dc5d13-c9b9-4ef5-af54-d8a9b0cd548c
-- title:
--   L4: wtot bound
-- statement:
--   The L4 construction uses the wtot bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L292-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L292-L314

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

theorem Formalism.InvariantFactorPaths.L4.wtot_bound (hs : 1 ≤ s) (hv : LL.vec (Fin.last K) = true) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hcd : c < LL.total)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1))
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0) :
    ∀ (μ ν : Fin (s + 1) → ℤ) (x y : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]), x ≠ 0 → y ≠ 0 →
      x ∈ Wtot p LL J M (Fin.last s) → y ∈ Wtot p LL J M (Fin.last s) → G.IsWt μ x → G.IsWt ν y →
      ∀ i, |ν i - μ i| ≤ ((4 * LL.total : ℕ) : ℤ) := by sorry
