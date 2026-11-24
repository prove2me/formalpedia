-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_copy_trunc
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.copy_trunc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:00:55.30861+00:00
-- url     : https://prove2.me/theorems/b68f879f-f284-4dae-a576-22c23354dc1b
-- title:
--   Germ D: copy trunc
-- statement:
--   The Germ D construction uses the copy trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/GermDJet.lean#L172-L177

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
variable {R : Type} [CommRing R] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.copy_trunc (m : ℕ) (i : Fin 2) :
    (jetTrunc : Jet R (Fin 2 × Fin d) (m + 1) →ₐ[R] _).comp (jetCopy d (m + 1) i) =
      (jetCopy d m i).comp (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] _) := by sorry
