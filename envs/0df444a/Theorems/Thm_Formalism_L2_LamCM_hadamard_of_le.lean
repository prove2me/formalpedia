-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_hadamard_of_le
-- name    : Formalism.L2.LamCM.hadamard_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:33.967747+00:00
-- url     : https://prove2.me/theorems/7fe9bf17-2391-496f-8519-1b1f72c2fc89
-- title:
--   Lam CM: hadamard of le
-- statement:
--   The Lam CM construction uses the hadamard of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L155-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L155-L233

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
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.hadamard_of_le (g : ℕ) (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (u : Fin g → Fin g → K)
    (H : (K →+* ℂ) → Matrix (Fin g) (Fin g) ℂ) (La : ℝ) (hLam : abelian₂.I ≠ 0) (hℓ : ∀ j, (ℓ j).Good)
    (hdne : (Matrix.of u).det ≠ 0) (hLa : 0 < La) (hH : ∀ σ, (H σ).PosDef)
    (hn : ∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re)
    (hle : (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ (Matrix.of u).det ≤ abelian₂.I)
    (hsq : ∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (u j)) ≤ (La * (ℓ j).n σ) ^ 2) :
    ∑ j, (ℓ j).deg - (g : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log La ≤ abelian₂.deg := by sorry
