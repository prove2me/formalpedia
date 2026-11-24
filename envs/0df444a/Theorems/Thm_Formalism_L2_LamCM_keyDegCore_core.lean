-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_keyDegCore_core
-- name    : Formalism.L2.LamCM.keyDegCore_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:18.185792+00:00
-- url     : https://prove2.me/theorems/c1f094db-726a-4d54-b4f3-bfc0d9e23fbf
-- title:
--   Lam CM: key Deg Core core
-- statement:
--   The Lam CM construction uses the key Deg Core core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L22-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L22-L100

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_HadamardLoc0
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_DetValuationLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors ComplexOrder

theorem Formalism.L2.LamCM.keyDegCore_core (hKF : KeyCore) (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K)
    (hT : T.Good) (hL : abelian₂.Good) (hloc : ∀ p, KeyLocAt x T abelian₂ p) (harch : ∀ σ, KeyArchAt x T abelian₂ σ)
    (hN : ∀ k : K, k ≠ 0 → ∑ σ : K →+* ℂ, Real.log ‖σ k‖ =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ))
    (hS : ∀ (I : FractionalIdeal (𝓞 K)⁰ K) (k : K), I ≠ 0 → k ≠ 0 →
      (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K k ≤ p.valuation K c ∧
        p.valuation K k⁻¹ ≤ p.valuation K c⁻¹) → FractionalIdeal.spanSingleton (𝓞 K)⁰ k = I) :
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by sorry
