-- Prove2me | Theorems.Thm_Formalism_L2_NX_tvAt_mem
-- name    : Formalism.L2.NX.tvAt_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:37.382197+00:00
-- url     : https://prove2.me/theorems/de7261ff-5e00-45f2-9ed2-3485ea82e059
-- title:
--   NX: tv At mem
-- statement:
--   The NX construction uses the tv At mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L216-L222

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
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}

theorem Formalism.L2.NX.tvAt_mem [DecidableEq ι] (hr : 2 ≤ r) (x : ι) : tvAt (p := p) hr x ∈ Uup p r := by sorry
