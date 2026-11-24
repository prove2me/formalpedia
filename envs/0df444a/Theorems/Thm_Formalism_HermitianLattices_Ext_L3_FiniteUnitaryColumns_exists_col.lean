-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_exists_col
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:28.046895+00:00
-- url     : https://prove2.me/theorems/30e2190c-37ee-4323-a676-176ea9396b45
-- title:
--   Finite Unitary Columns: exists col
-- statement:
--   The Finite Unitary Columns construction uses the exists col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L80-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L80-L124

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_col {m : ℕ} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (x : Fin (m + 1) → k) (hx : ∑ i, σ (x i) * x i = 1) :
    ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) k, cj σ g * g = 1 ∧ ∀ i, g i 0 = x i := by sorry
