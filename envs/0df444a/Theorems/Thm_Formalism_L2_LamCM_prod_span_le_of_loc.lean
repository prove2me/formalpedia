-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_prod_span_le_of_loc
-- name    : Formalism.L2.LamCM.prod_span_le_of_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:48.711066+00:00
-- url     : https://prove2.me/theorems/c1a80c09-de32-4fb9-b5fe-56e30cb220f5
-- title:
--   Lam CM: prod span le of loc
-- statement:
--   The Lam CM construction uses the prod span le of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L132-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/DetValuationLeOne.lean#L132-L153

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

theorem Formalism.L2.LamCM.prod_span_le_of_loc {g : ℕ} (abelian₂ : MLine K) (ℓ : Fin g → MLine K) (d : K) (hLam : abelian₂.I ≠ 0)
    (hℓ : ∀ j, (ℓ j).I ≠ 0) (hd : d ≠ 0)
    (hloc : ∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin g → K), IsLocGen p cd abelian₂.I ∧
      (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * d) ≤ p.valuation K cd) :
    (∏ j, (ℓ j).I) * FractionalIdeal.spanSingleton (𝓞 K)⁰ d ≤ abelian₂.I := by sorry
