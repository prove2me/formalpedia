-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_jetMap_mk
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:03.653799+00:00
-- url     : https://prove2.me/theorems/5f1bc3a8-8991-47ab-986e-09ef308ffcf9
-- title:
--   Germ D: jet Map mk
-- statement:
--   The Germ D construction uses the jet Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L16-L17

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open AlgebraicGeometry CategoryTheory MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] {ι : Type} {m : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') (p : MvPolynomial ι R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (aeval φ p) := by sorry
