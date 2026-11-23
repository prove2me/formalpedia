-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_subst
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:10.907838+00:00
-- url     : https://prove2.me/theorems/bbc25ccb-8823-47be-9aaa-7a5af2dd0e31
-- title:
--   FBId Jet: ps Jet subst
-- statement:
--   The FBId Jet construction uses the ps Jet subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L261-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/FBIdJet.lean#L261-L331

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst {σ τ : Type} [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] (m : ℕ)
    (a : σ → MvPowerSeries τ R) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) :
    psJet m (MvPowerSeries.subst a f) =
      jetMap (fun i => psTrunc m (a i)) (fun i => psTrunc_mem_orig m (a i) (ha i)) (psJet m f) := by sorry
