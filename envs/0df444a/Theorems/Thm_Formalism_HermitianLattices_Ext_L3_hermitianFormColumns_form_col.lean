-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_form_col
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.form_col
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:38.354051+00:00
-- url     : https://prove2.me/theorems/ec25b516-54ec-4aad-baa4-91ddcd7b3c99
-- title:
--   hermitian Form Columns: form col
-- statement:
--   The hermitian Form Columns construction uses the form col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L21-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {A : Type*} [CommRing A] [StarRing A] {m : Type} [Fintype m] [DecidableEq m]

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.form_col (H : Matrix m m A) (x y : m → A) (a b : Unit) :
    ((colU x)ᴴ * H * colU y) a b = star x ⬝ᵥ (H *ᵥ y) := by sorry
