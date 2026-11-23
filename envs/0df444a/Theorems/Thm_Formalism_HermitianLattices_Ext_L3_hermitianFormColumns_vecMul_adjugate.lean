-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_vecMul_adjugate
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.vecMul_adjugate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:26:28.937689+00:00
-- url     : https://prove2.me/theorems/45c14e3f-579a-4ae2-91e0-0bb767c6e603
-- title:
--   hermitian Form Columns: vec Mul adjugate
-- statement:
--   The hermitian Form Columns construction uses the vec Mul adjugate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L140-L142

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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {A : Type*} [CommRing A] [StarRing A]

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.vecMul_adjugate (H : Matrix m m A) (x : m → A) :
    (x ᵥ* H) ᵥ* H.adjugate = H.det • x := by sorry
