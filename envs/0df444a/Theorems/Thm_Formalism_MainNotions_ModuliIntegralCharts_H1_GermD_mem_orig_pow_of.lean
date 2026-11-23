-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_mem_orig_pow_of
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.mem_orig_pow_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:51.839348+00:00
-- url     : https://prove2.me/theorems/1740223b-50b3-4640-98e8-0809598df041
-- title:
--   Germ D: mem orig pow of
-- statement:
--   The Germ D construction uses the mem orig pow of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L39-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L39-L42

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.mem_orig_pow_of {n : ℕ} {p : MvPolynomial ι R} (h : ∀ e ∈ p.support, n ≤ e.degree) :
    p ∈ orig R ι ^ n := by sorry
