-- Prove2me | Theorems.Thm_Formalism_L2_NX_glOf_val
-- name    : Formalism.L2.NX.glOf_val
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:45:41.200874+00:00
-- url     : https://prove2.me/theorems/e4266598-18bb-4e9d-8a9f-f5b2eb1b33eb
-- title:
--   NX: gl Of val
-- statement:
--   The NX construction uses the gl Of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L340-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L340-L344

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem Formalism.L2.NX.glOf_val {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) (h : IsUnit M.det) :
    ((glOf M : GL ι R) : Matrix ι ι R) = M := by sorry
