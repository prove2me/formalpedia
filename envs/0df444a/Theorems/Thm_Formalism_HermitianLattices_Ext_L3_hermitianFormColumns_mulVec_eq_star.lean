-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_mulVec_eq_star
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.mulVec_eq_star
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:51:29.964864+00:00
-- url     : https://prove2.me/theorems/868f36af-b12b-5001-a823-e37771f89a05
-- title:
--   hermitian Form Columns: mul Vec eq star
-- statement:
--   The hermitian Form Columns construction uses the mul Vec eq star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L120-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L120-L127

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

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.mulVec_eq_star {H : Matrix m m A} (hH : Hᴴ = H) (x : m → A) :
    H *ᵥ x = star (star x ᵥ* H) := by sorry
