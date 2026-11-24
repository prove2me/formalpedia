-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_exists_refl
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_refl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:37.561808+00:00
-- url     : https://prove2.me/theorems/6ef788de-5710-4ea9-acb5-bfea6b40cc38
-- title:
--   Finite Unitary Columns: exists refl
-- statement:
--   The Finite Unitary Columns construction uses the exists refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L29-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L29-L73

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_refl {n : Type*} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (x y : n → k) (hx : ∑ i, σ (x i) * x i = 1)
    (hy : ∑ i, σ (y i) * y i = 1) (hxy : ∑ i, σ (y i) * x i ≠ 1) :
    ∃ g : Matrix n n k, cj σ g * g = 1 ∧ g *ᵥ x = y := by sorry
