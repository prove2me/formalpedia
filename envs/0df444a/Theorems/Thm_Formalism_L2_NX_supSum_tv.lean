-- Prove2me | Theorems.Thm_Formalism_L2_NX_supSum_tv
-- name    : Formalism.L2.NX.supSum_tv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:56.640857+00:00
-- url     : https://prove2.me/theorems/9d8d247f-cb10-491a-96e5-5b47fe8285dc
-- title:
--   NX: sup Sum tv
-- statement:
--   The NX construction uses the sup Sum tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L176-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L176-L199

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

theorem Formalism.L2.NX.supSum_tv {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : supSum r (tv hr c) = c := by sorry
