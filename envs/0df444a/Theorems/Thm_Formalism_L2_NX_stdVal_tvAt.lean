-- Prove2me | Theorems.Thm_Formalism_L2_NX_stdVal_tvAt
-- name    : Formalism.L2.NX.stdVal_tvAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:34.492653+00:00
-- url     : https://prove2.me/theorems/c9bcbaa6-a195-40ca-b1b5-934610e83c21
-- title:
--   NX: std Val tv At
-- statement:
--   The NX construction uses the std Val tv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L224-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L224-L232

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

theorem Formalism.L2.NX.stdVal_tvAt [DecidableEq ι] {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ)
    (hr : 2 ≤ r) (x : ι) : stdVal p r θ (tvAt hr x) = θ x (Multiplicative.ofAdd 1) := by sorry
