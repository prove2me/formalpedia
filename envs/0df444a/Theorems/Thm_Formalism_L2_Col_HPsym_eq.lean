-- Prove2me | Theorems.Thm_Formalism_L2_Col_HPsym_eq
-- name    : Formalism.L2.Col.HPsym_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:55.247506+00:00
-- url     : https://prove2.me/theorems/d9b70998-8f16-4c81-a06a-8148124cc299
-- title:
--   Col: HPsym eq
-- statement:
--   The Col construction uses the HPsym eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L785-L807
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L785-L807

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ]

theorem Formalism.L2.Col.HPsym_eq (k rS : ℕ) : ((HPsym κ n k rS : Subgroup (GL (Fin n) κ)) : Set (GL (Fin n) κ)) =
    uSet κ (fun i j : Fin n => i < j ∧ ¬ (rS ≤ i.val ∧ i.val < rS + k ∧ j.val = rS + k)) := by sorry
