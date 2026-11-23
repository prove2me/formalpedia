-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_mk
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:27.074581+00:00
-- url     : https://prove2.me/theorems/a88ea2fb-06e8-414f-a94b-1778d1f83906
-- title:
--   hermitian Form Columns: Qc mk
-- statement:
--   The hermitian Form Columns construction uses the Qc mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L154-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L154-L165

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

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_mk {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K)) (x : m → 𝓞 K) :
    Qc 𝔭 k c H (fun i => mkk K 𝔭 k (x i)) ↔ ∃ j, (star x ᵥ* H) j ∉ extP K 𝔭 ^ (c + 1) := by sorry
