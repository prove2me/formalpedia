-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_cj
-- name    : Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_cj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:55.132511+00:00
-- url     : https://prove2.me/theorems/fa892258-5460-41f7-9550-6a267467b3aa
-- title:
--   Finite Unitary Columns: cj cj
-- statement:
--   The Finite Unitary Columns construction uses the cj cj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardUnitaryFin.lean#L75-L78

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

theorem Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.cj_cj {n n' : Type*} (σ : k ≃+* k) (hσ : ∀ x, σ (σ x) = x) (X : Matrix n n' k) :
    cj σ (cj σ X) = X := by sorry
