-- Prove2me | Theorems.Thm_Formalism_FG_LowCoefficients_coeff_expand_eq_zero
-- name    : Formalism.FG.LowCoefficients.coeff_expand_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:06.93014+00:00
-- url     : https://prove2.me/theorems/32cd3c3b-a7e2-42d9-bf51-d249bb631be5
-- title:
--   Low Coefficients: coeff expand eq zero
-- statement:
--   The Low Coefficients construction uses the coeff expand eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffExpandEqZero.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffExpandEqZero.lean#L11-L35

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.LowCoefficients
open Formalism.G

theorem Formalism.FG.LowCoefficients.coeff_expand_eq_zero {R : Type*} [CommRing R] {τ : Type*} (q : ℕ) (hq : q ≠ 0)
    (hq2 : 2 ≤ q) (φ : MvPowerSeries τ R) (N : ℕ) (hN : 1 ≤ N)
    (hlow : ∀ m : τ →₀ ℕ, m.degree < N → MvPowerSeries.coeff m φ = 0)
    (d : τ →₀ ℕ) (hd : d.degree = N) : MvPowerSeries.coeff d (MvPowerSeries.expand q hq φ) = 0 := by sorry
