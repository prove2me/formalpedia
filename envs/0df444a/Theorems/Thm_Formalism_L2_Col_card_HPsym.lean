-- Prove2me | Theorems.Thm_Formalism_L2_Col_card_HPsym
-- name    : Formalism.L2.Col.card_HPsym
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:21.572739+00:00
-- url     : https://prove2.me/theorems/b9fe9019-43f5-4195-905c-5e13c8a2eee3
-- title:
--   Col: card HPsym
-- statement:
--   The Col construction uses the card HPsym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L849-L856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L849-L856

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
variable {n : ℕ} {κ : Type} [CommRing κ]

theorem Formalism.L2.Col.card_HPsym (κ : Type) [CommRing κ] (n k rS : ℕ) (hn : rS + k < n) :
    Nat.card ↥(HPsym κ n k rS) = Nat.card κ ^ (n * (n - 1) / 2 - k) := by sorry
