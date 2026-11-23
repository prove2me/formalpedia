-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamGen_nil
-- name    : Formalism.L2.Col.lamGen_nil
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:58.625441+00:00
-- url     : https://prove2.me/theorems/7c1f05ec-5cb4-4990-8195-d0e709559da4
-- title:
--   Col: lam Gen nil
-- statement:
--   The Col construction uses the lam Gen nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L55-L58

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

theorem Formalism.L2.Col.lamGen_nil (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n a : ℕ) (S : Finset ℕ) :
    lamGen ψ χ n a [] S = supChar ψ n a [] S := by sorry
