-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_eval_fg
-- name    : CompanionTheory.HeckeA.eval_fg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:51.856946+00:00
-- url     : https://prove2.me/theorems/a0318afd-8a95-4efe-8050-e88ae1c3ce7a
-- title:
--   Hecke A: eval fg
-- statement:
--   The Hecke A construction uses the eval fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L88-L90

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Theorems.Thm_UpperTheory_Reformulated_B_Qn15_eval_fg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Formalism.UG.P
noncomputable section
open CompanionTheory CompanionTheory.HeckeA
variable {G H W : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ι : H →* G) (K : Subgroup H)
variable {K}
variable {R : Type} [CommRing R] [Algebra R ℂ]

theorem CompanionTheory.HeckeA.eval_fg {σ : Type} {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (P : MvPolynomial σ ℂ) :
    ∃ M : Submodule R ℂ, M.FG ∧ ∀ v : σ → ℂ, (∀ i, v i ∈ M₀) → MvPolynomial.eval v P ∈ M := by sorry
