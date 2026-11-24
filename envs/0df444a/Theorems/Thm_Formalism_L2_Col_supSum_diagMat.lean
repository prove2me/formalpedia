-- Prove2me | Theorems.Thm_Formalism_L2_Col_supSum_diagMat
-- name    : Formalism.L2.Col.supSum_diagMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:19.618626+00:00
-- url     : https://prove2.me/theorems/875684cc-c9a0-487a-8f6f-cd853ddd9408
-- title:
--   Col: sup Sum diag Mat
-- statement:
--   The Col construction uses the sup Sum diag Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L683-L713
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L683-L713

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

theorem Formalism.L2.Col.supSum_diagMat {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (S : Finset ℕ) (g : Matrix (Fin s) (Fin s) κ) :
    supSum a S (diagMat s n g) = supSum a S g := by sorry
