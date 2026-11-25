-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_lattice_inclusion_forms_injective
-- name    : Formalism.L2.FormalSeriesBounds.lattice_inclusion_forms_injective
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:22.901867+00:00
-- url     : https://prove2.me/theorems/fd9a1fd9-98fc-4caf-8e42-d2493bb567d3
-- title:
--   Formal Series Bounds: lattice inclusion forms injective
-- statement:
--   The Formal Series Bounds construction uses the lattice inclusion forms injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L254-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CartesianBoundOnCurves.lean#L254-L256

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem Formalism.L2.FormalSeriesBounds.lattice_inclusion_forms_injective (X : Cart V d I J) : LatticeInclusionFormsInjective X := by sorry
