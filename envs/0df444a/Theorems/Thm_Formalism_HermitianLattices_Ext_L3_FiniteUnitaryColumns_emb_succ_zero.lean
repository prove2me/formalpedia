-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:16.494987+00:00
-- url     : https://prove2.me/theorems/22a24e9c-544c-4713-a959-8d8b69752e55
-- title:
--   Finite Unitary Columns: emb succ zero
-- statement:
--   The Finite Unitary Columns construction uses the emb succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L133-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L133-L134

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero {m : ℕ} (Y : Matrix (Fin m) (Fin m) k) (i : Fin m) :
    emb Y i.succ 0 = 0 := by sorry

attribute [defeq] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
