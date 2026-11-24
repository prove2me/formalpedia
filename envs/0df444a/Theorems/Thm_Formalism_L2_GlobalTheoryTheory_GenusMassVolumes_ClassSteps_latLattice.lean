-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_GenusMassVolumes_ClassSteps_latLattice
-- name    : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps.latLattice
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:44.007402+00:00
-- url     : https://prove2.me/theorems/560d7cf7-d0e4-485b-8240-1be3bc456410
-- title:
--   Class Steps: lat Lattice
-- statement:
--   The Class Steps construction uses the lat Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL5/PClassSteps.lean#L87-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL5/PClassSteps.lean#L87-L165

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_UJClassMassOfOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL5_PClassSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps
open NumberField PI.UJClassFin PI.UJClassMass PI.UnitaryGroupMassFormula.UJClassMass Formalism.HermitianLatticesTheory
open scoped TensorProduct ComplexOrder

theorem Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps.latLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (V : Type) [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [FiniteDimensional E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (M : ℕ) (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    Submodule.IsLattice E L0 →
    (∀ τ : E →+* ℂ, HasSignature ((gramOf h b).map τ) M 0) →
    ∀ g : HA (AF F) σ (gramOf h b), ∃ N : Submodule (𝓞 E) V,
      (N : Set V) = latSet σ (gramOf h b) b L0 g ∧ Submodule.IsLattice E N := by sorry
