-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_nkB_le
-- name    : Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkB_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:40.196896+00:00
-- url     : https://prove2.me/theorems/f6cce7f1-02e7-447b-a81d-5a4877fe2ab0
-- title:
--   vector Count Bounds: nk B le
-- statement:
--   The vector Count Bounds construction uses the nk B le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L164-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEleventh.lean#L164-L237

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

theorem Formalism.HermitianLattices.Ext.L3.vectorCountBounds.nkB_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D : 𝓞 F} (hD : H.det = ι D) {d : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (n : 𝓞 F) (k : ℕ) (hdk : d + 1 ≤ k + 2) :
    ∃ n' : 𝓞 F, nkB 𝔭 (k + 2) d H n ≤ Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n' := by sorry
