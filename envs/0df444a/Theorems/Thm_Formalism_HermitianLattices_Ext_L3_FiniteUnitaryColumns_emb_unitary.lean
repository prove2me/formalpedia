-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_unitary
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:47:05.913059+00:00
-- url     : https://prove2.me/theorems/f15f9d6d-f596-4fec-bbfb-3ee1cd502eb9
-- title:
--   Finite Unitary Columns: emb unitary
-- statement:
--   The Finite Unitary Columns construction uses the emb unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L142-L151

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_unitary {m : ℕ} (σ : k ≃+* k) (Y : Matrix (Fin m) (Fin m) k) (h : cj σ Y * Y = 1) :
    cj σ (emb Y) * emb Y = 1 := by sorry
