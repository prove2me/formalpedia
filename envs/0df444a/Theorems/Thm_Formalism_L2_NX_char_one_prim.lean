-- Prove2me | Theorems.Thm_Formalism_L2_NX_char_one_prim
-- name    : Formalism.L2.NX.char_one_prim
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:55.529817+00:00
-- url     : https://prove2.me/theorems/0e07a13e-700d-4cda-ae41-5fa98934b697
-- title:
--   NX: char one prim
-- statement:
--   The NX construction uses the char one prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L142-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L142-L149

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

theorem Formalism.L2.NX.char_one_prim {K : Type} [Field K] {q : ℕ} (hq : q.Prime) (θ : Multiplicative (ZMod q) →* Kˣ) (hθ : θ ≠ 1) :
    IsPrimitiveRoot (((θ (Multiplicative.ofAdd 1) : Kˣ)) : K) q := by sorry
