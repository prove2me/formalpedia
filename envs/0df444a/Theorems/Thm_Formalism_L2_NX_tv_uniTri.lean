-- Prove2me | Theorems.Thm_Formalism_L2_NX_tv_uniTri
-- name    : Formalism.L2.NX.tv_uniTri
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:51.344684+00:00
-- url     : https://prove2.me/theorems/1e269143-7bb7-455b-8d69-2e8ce8c12379
-- title:
--   NX: tv uni Tri
-- statement:
--   The NX construction uses the tv uni Tri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L160-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean#L160-L174

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

theorem Formalism.L2.NX.tv_uniTri {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : IsUniTri r (tv hr c) := by sorry
