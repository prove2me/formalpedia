-- Prove2me | Theorems.Thm_Formalism_L2_NX_charOf_one
-- name    : Formalism.L2.NX.charOf_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:53.020517+00:00
-- url     : https://prove2.me/theorems/c6578084-b80a-405c-963c-fa61e28bbf4e
-- title:
--   NX: char Of one
-- statement:
--   The NX construction uses the char Of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L239-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L239-L244

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

theorem Formalism.L2.NX.charOf_one {K : Type} [Field K] {q : ℕ} (ζ : Kˣ) (hζ : ζ ^ q = 1) :
    charOf ζ hζ (Multiplicative.ofAdd 1) = ζ := by sorry
