-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_KAV_coeff_foldr
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_foldr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:14.372136+00:00
-- url     : https://prove2.me/theorems/055e6421-da8d-4e1a-b9b3-fbdf081ffd47
-- title:
--   KAV: coeff foldr
-- statement:
--   The KAV construction uses the coeff foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L51-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffPolyAdd.lean#L51-L70

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEncPf
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsExpChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffPolyAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.KAV
open MvPowerSeries

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.KAV.coeff_foldr {σ κ R : Type} [CommRing R] (φ : κ → σ) (m : κ → ℕ) (F : MvPowerSeries σ R) :
    ∀ (L : List κ), L.Nodup → (∀ p ∈ L, ∀ q ∈ L, φ p = φ q → p = q) → ∀ N : σ →₀ ℕ, (∀ p ∈ L, N (φ p) = 0) →
      coeff N (L.foldr (fun p g => (pderiv R (φ p))^[m p] g) F) =
        (L.map fun p => ((m p).factorial : R)).prod * coeff (N + (L.map fun p => m p • Finsupp.single (φ p) 1).sum) F
  := by sorry
