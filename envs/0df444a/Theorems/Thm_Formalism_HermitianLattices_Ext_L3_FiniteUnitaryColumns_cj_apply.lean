-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:24.395792+00:00
-- url     : https://prove2.me/theorems/1ba30fed-ef1f-4b25-b522-cc88f179b5cc
-- title:
--   Finite Unitary Columns: cj apply
-- statement:
--   The Finite Unitary Columns construction uses the cj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L15-L16

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_apply {n n' : Type*} (σ : k ≃+* k) (X : Matrix n n' k) (i : n') (j : n) :
    cj σ X i j = σ (X j i) := by sorry
