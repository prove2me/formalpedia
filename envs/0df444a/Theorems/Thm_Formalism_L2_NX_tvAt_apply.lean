-- Prove2me | Theorems.Thm_Formalism_L2_NX_tvAt_apply
-- name    : Formalism.L2.NX.tvAt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:45.616645+00:00
-- url     : https://prove2.me/theorems/5c2f6091-a740-4041-be6b-d951ae73933f
-- title:
--   NX: tv At apply
-- statement:
--   The NX construction uses the tv At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L205-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L205-L214

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

theorem Formalism.L2.NX.tvAt_apply [DecidableEq ι] (hr : 2 ≤ r) (x y : ι) :
    ((tvAt (p := p) hr x y : GL (Fin r) (ZMod (p y))) : Matrix (Fin r) (Fin r) (ZMod (p y))) =
      if y = x then tv hr 1 else 1 := by sorry
