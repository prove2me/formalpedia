-- Prove2me | Theorems.Thm_Formalism_L2_Col_sub_mul
-- name    : Formalism.L2.Col.sub_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:26.491537+00:00
-- url     : https://prove2.me/theorems/8986cddb-1343-408f-a651-49891e2f6d20
-- title:
--   Col: sub mul
-- statement:
--   The Col construction uses the sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L105-L109

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.sub_mul {s : ℕ} (A B : Matrix (Fin (s + 1)) (Fin (s + 1)) κ) (hA : ∀ i : Fin s, A i.castSucc (Fin.last s) = 0) :
    (A * B).submatrix Fin.castSucc Fin.castSucc = A.submatrix Fin.castSucc Fin.castSucc * B.submatrix Fin.castSucc Fin.castSucc := by sorry
