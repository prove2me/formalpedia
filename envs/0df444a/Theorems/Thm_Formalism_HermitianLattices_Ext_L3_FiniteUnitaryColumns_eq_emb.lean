-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_eq_emb
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.eq_emb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:27.676958+00:00
-- url     : https://prove2.me/theorems/f91a53f2-7020-4ddc-9b73-7bd21e2549e8
-- title:
--   Finite Unitary Columns: eq emb
-- statement:
--   The Finite Unitary Columns construction uses the eq emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L153-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L153-L173

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.eq_emb {m : ℕ} (σ : k ≃+* k) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
    (h : cj σ Z * Z = 1) (h0 : Z 0 0 = 1) (hs : ∀ i : Fin m, Z i.succ 0 = 0) :
    Z = emb (Z.submatrix Fin.succ Fin.succ) ∧
      cj σ (Z.submatrix Fin.succ Fin.succ) * Z.submatrix Fin.succ Fin.succ = 1 := by sorry
