-- Prove2me | Theorems.Thm_Formalism_L2_NX_mem_Uup
-- name    : Formalism.L2.NX.mem_Uup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:11.201186+00:00
-- url     : https://prove2.me/theorems/30255cb9-5096-4473-99e2-2072eaffaa7f
-- title:
--   NX: mem Uup
-- statement:
--   The NX construction uses the mem Uup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L61-L62

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
variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)
variable {r}
variable (r)
variable {p r}

theorem Formalism.L2.NX.mem_Uup {g : GProd p r} : g ∈ Uup p r ↔
    ∀ x, IsUniTri r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) := by sorry
