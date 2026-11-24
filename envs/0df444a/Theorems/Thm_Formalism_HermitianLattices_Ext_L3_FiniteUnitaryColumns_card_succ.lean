-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_card_succ
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.card_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:27.504906+00:00
-- url     : https://prove2.me/theorems/ceb12789-a13b-4155-bc61-b94b978aa5dc
-- title:
--   Finite Unitary Columns: card succ
-- statement:
--   The Finite Unitary Columns construction uses the card succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L175-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L175-L229

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.card_succ {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) :
    Nat.card {X : Matrix (Fin (m + 1)) (Fin (m + 1)) k // cj σ X * X = 1} =
      Nat.card {x : Fin (m + 1) → k // ∑ i, σ (x i) * x i = 1} *
        Nat.card {X : Matrix (Fin m) (Fin m) k // cj σ X * X = 1} := by sorry
