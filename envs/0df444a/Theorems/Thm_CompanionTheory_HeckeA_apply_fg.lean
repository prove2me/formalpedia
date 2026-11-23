-- Prove2me | Theorems.Thm_CompanionTheory_HeckeA_apply_fg
-- name    : CompanionTheory.HeckeA.apply_fg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:31:37.81642+00:00
-- url     : https://prove2.me/theorems/80680329-9fb8-488c-9ab5-55b9061f544f
-- title:
--   Hecke A: apply fg
-- statement:
--   The Hecke A construction uses the apply fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L92-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/HeckeA.lean#L92-L105

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalFg
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
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

theorem CompanionTheory.HeckeA.apply_fg [Module R W] [IsScalarTower R ℂ W] {σ κ : Type} [Fintype κ] [DecidableEq κ] (b : Module.Basis κ ℂ W)
    (P : κ → κ → MvPolynomial σ ℂ) {M₀ : Submodule R ℂ} (h₀ : M₀.FG) (w : W) :
    ∃ N : Submodule R W, N.FG ∧ ∀ (A : W →ₗ[ℂ] W) (v : σ → ℂ), (∀ i, v i ∈ M₀) →
      (LinearMap.toMatrix b b A = fun i j => MvPolynomial.eval v (P i j)) → A w ∈ N := by sorry
