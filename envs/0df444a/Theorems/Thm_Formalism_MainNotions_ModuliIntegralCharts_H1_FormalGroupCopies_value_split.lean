-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FormalGroupCopies_value_split
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.value_split
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:12:07.347594+00:00
-- url     : https://prove2.me/theorems/4232da9d-ca13-4e2b-8db2-8d4157c21601
-- title:
--   Formal Group Copies: value split
-- statement:
--   The Formal Group Copies construction uses the value split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L248-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FormalGroupCopies.lean#L248-L261

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupOnCopies
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PartialDerivativeExponent
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupCopies
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent
variable {R : Type} [CommRing R] {d n : ℕ}
variable {ι : Type} [Fintype ι] (F : Fin d → PS R 2 d) (cp : ι → Fin n) (u : ι → Fin d → R)

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies.value_split (S : Finset (Fin n)) (P₁ P₂ : MvPolynomial ι R) (h1 : ∀ l ∈ P₁.vars, cp l ∈ S)
    (h2 : ∀ l ∈ P₂.vars, cp l ∉ S) (f₁ f₂ ES ET : PS R n d) (hf1 : f₁ ∈ subV R (Vc d S))
    (hf2 : f₂ ∈ subV R (Vc d Sᶜ)) (hES : ES ∈ subV R (Vc d S)) (hET : ET ∈ subV R (Vc d Sᶜ))
    (c1 : constantCoeff ES = 1) (c2 : constantCoeff ET = 1) :
    constantCoeff (DpolyN F cp u (P₁ * P₂) (f₁ * f₂ * (ES * ET))) =
      constantCoeff (DpolyN F cp u P₁ (f₁ * (ES * ET))) *
        constantCoeff (DpolyN F cp u P₂ (f₂ * (ES * ET))) := by sorry
