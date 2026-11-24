-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_nkM_eq_add
-- name    : Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkM_eq_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:25.941562+00:00
-- url     : https://prove2.me/theorems/cc790a1a-02b5-471e-b1fb-4081ef501729
-- title:
--   vector Count Bounds: nk M eq add
-- statement:
--   The vector Count Bounds construction uses the nk M eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L86-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L86-L104

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEleventh
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.vectorCountBounds
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms hermitianFormColumns
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkM_eq_add {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k c : ℕ) (H : Matrix m m (𝓞 K)) (n : 𝓞 F) :
    nkM 𝔭 k H n = nkQ 𝔭 k c H n + nkB 𝔭 k c H n := by sorry
