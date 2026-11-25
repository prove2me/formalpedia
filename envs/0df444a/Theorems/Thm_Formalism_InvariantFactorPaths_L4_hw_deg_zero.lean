-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_hw_deg_zero
-- name    : Formalism.InvariantFactorPaths.L4.hw_deg_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:55:38.749808+00:00
-- url     : https://prove2.me/theorems/31a7a852-59d2-4ea8-a513-9dc8641f79bb
-- title:
--   L4: hw deg zero
-- statement:
--   The L4 construction uses the hw deg zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L404-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeKillsDegreeZero.lean#L404-L469

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

theorem Formalism.InvariantFactorPaths.L4.hw_deg_zero (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (hcomp : ∀ μ x m, coeff m (G.comp μ x) = if wtX LL c m = μ then coeff m x else 0)
    (la : Fin (s + 1) → ℤ) (h : MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (hh : G.IsHW la h)
    (hW : h ∈ Wtot p LL J M (Fin.last s)) : h ∈ XSp p (setLast LL 0) J M (Fin.last s) := by sorry
