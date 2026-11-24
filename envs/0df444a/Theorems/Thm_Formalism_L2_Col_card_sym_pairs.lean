-- Prove2me | Theorems.Thm_Formalism_L2_Col_card_sym_pairs
-- name    : Formalism.L2.Col.card_sym_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:02.960166+00:00
-- url     : https://prove2.me/theorems/20354e63-3101-4a61-a53e-59f0514745e4
-- title:
--   Col: card sym pairs
-- statement:
--   The Col construction uses the card sym pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L809-L847
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L809-L847

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

theorem Formalism.L2.Col.card_sym_pairs (k rS : ℕ) (hn : rS + k < n) :
    Nat.card {p : Fin n × Fin n // p.1 < p.2 ∧ ¬ (rS ≤ p.1.val ∧ p.1.val < rS + k ∧ p.2.val = rS + k)} = n * (n - 1) / 2 - k := by sorry
