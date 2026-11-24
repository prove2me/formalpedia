-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_ETerm_term_bound
-- name    : Formalism.InvariantFactorPaths.G7.ETerm.term_bound
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:56.48636+00:00
-- url     : https://prove2.me/theorems/f87ae7f4-985c-41f3-ac2a-62149871ac06
-- title:
--   ETerm: term bound
-- statement:
--   The ETerm construction uses the term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L397-L487
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/NormNatCastLeOfDvd.lean#L397-L487

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormNatCastLeOfDvd
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_C_mul_right
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_eq_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_jetPair_sum_right
import Theorems.Thm_Formalism_LT_ExpP_term_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.ETerm
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)
variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]

theorem Formalism.InvariantFactorPaths.G7.ETerm.term_bound (h1 : JetPairingHasseIdentity) (h2 : HasseDerivIntegralHomogeneous) (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K)
    (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K)
    (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) (hp : p.Prime) (hpn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (haA : ∀ φ, ‖aA φ‖ ≤ 1) (haB : ∀ k, ‖aB k‖ ≤ 1) (hb : ∀ k x, ‖b k x‖ ≤ 1) (hZ : Integral Z)
    (hY : Integral Y) (hZlow : LowGe p Z) (hQ : ∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1)
    (i : ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (hk : ∑ j, k j = i) (U : MvPowerSeries (Tp ⊕ Lw) K)
    (hU : Integral U) :
    ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
        jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U)) = 0 ∨
      ∃ w, valid p aA dA aB dB b e Q w ∧
        ‖((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U))‖ ≤
          bnd K p e w := by sorry
