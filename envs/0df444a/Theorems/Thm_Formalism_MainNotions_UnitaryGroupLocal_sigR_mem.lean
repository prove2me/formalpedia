-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnitaryGroupLocal_sigR_mem
-- name    : Formalism.MainNotions.UnitaryGroupLocal.sigR_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:05.842725+00:00
-- url     : https://prove2.me/theorems/23fb048f-1198-57ca-8fc3-8320afa10e40
-- title:
--   Unitary Group Local: sig R mem
-- statement:
--   The Unitary Group Local construction uses the sig R mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnitaryGroupLocal.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/UnitaryGroupLocal.lean#L86-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApprox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnitaryGroupLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnitaryGroupLocal
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain Topology Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (v : HeightOneSpectrum (𝓞 F))

theorem Formalism.MainNotions.UnitaryGroupLocal.sigR_mem (σ : E →ₐ[F] E) {x : E ⊗[F] v.adicCompletion F} (hx : x ∈ oE v) :
    PI.UnitaryApproxDefs.sigR σ (v.adicCompletion F) x ∈ oE v := by sorry
