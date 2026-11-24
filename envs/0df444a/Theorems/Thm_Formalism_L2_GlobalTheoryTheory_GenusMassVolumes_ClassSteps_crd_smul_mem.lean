-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_GenusMassVolumes_ClassSteps_crd_smul_mem
-- name    : Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps.crd_smul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:55:12.144867+00:00
-- url     : https://prove2.me/theorems/c761d688-6a84-4590-87c6-1918af337d1f
-- title:
--   Class Steps: crd smul mem
-- statement:
--   The Class Steps construction uses the crd smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL5/PClassSteps.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL5/PClassSteps.lean#L17-L26

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.ClassSteps.crd_smul_mem {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] {M : ℕ}
    (b : Module.Basis (Fin M) E V) (L0 : Submodule (𝓞 E) V) (r : 𝓞 E) {x : Fin M → E} (hx : x ∈ crdOf b L0) :
    (r : E) • x ∈ crdOf b L0 := by sorry
