-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_card_unitary_fin
-- name    : Formalism.HermitianLattices.Ext.L3.card_unitary_fin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:41.046263+00:00
-- url     : https://prove2.me/theorems/37ef9b05-62bf-41af-b50a-b063f2d367f8
-- title:
--   L3: card unitary fin
-- statement:
--   The L3 construction uses the card unitary fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L235-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L235-L277

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3

theorem Formalism.HermitianLattices.Ext.L3.card_unitary_fin {k : Type*} [Field k] [Fintype k] (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x)
    (hne : ∃ x, σ x ≠ x) (q : ℕ) (hq : Fintype.card k = q ^ 2) (m : ℕ) :
    (Nat.card {X : Matrix (Fin m) (Fin m) k // (X.map σ).transpose * X = 1} : ℝ) =
      (q : ℝ) ^ (m ^ 2) * ∏ j ∈ Finset.Icc 1 m, (1 - (-(q : ℝ))⁻¹ ^ j) := by sorry
