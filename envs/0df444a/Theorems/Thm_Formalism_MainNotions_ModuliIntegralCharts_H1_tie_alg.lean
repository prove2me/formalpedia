-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_tie_alg
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.tie_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:00:04.228967+00:00
-- url     : https://prove2.me/theorems/45fccfb6-6963-40c6-8138-324c9cf9b106
-- title:
--   H1: tie alg
-- statement:
--   The H1 construction uses the tie alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L397-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpTieAlg.lean#L397-L411

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_MonoVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTieAlg
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj ExpTieAlg NumberField

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.tie_alg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {S : Type} [CommRing S]
    {d : ℕ} (F : Fin d → PS S 2 d) (uvec : Lt1 Dw → Fin d → S)
    (φ : Fin d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (hφ : IsExpOf F uvec φ) (α : Lt1 Dw →₀ ℕ) (g : PS S 1 d) :
    constantCoeff (DpolyOf F uvec (MvPolynomial.monomial α 1) g) = expVal (compL φ g) α := by sorry
