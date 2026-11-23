-- Prove2me | Theorems.Thm_Formalism_L2_NX_char_one_ne
-- name    : Formalism.L2.NX.char_one_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:42.362092+00:00
-- url     : https://prove2.me/theorems/2fbcf022-0fe5-4166-9a41-67e4f95a9fc8
-- title:
--   NX: char one ne
-- statement:
--   The NX construction uses the char one ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L133-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L133-L140

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
variable (r)
variable {r}
variable (p r)

theorem Formalism.L2.NX.char_one_ne {K : Type} [Field K] {q : ℕ} [NeZero q] (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    θ (Multiplicative.ofAdd 1) ≠ 1 := by sorry
