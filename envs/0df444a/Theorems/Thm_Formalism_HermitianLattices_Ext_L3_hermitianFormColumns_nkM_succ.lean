-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_nkM_succ
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.nkM_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:25.421238+00:00
-- url     : https://prove2.me/theorems/8f8dc2a8-2da0-44da-814e-4433318a738f
-- title:
--   hermitian Form Columns: nk M succ
-- statement:
--   The hermitian Form Columns construction uses the nk M succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L307-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L307-L316

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

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.nkM_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {H : Matrix m m (𝓞 K)} (hH : Hᴴ = H) {D n : 𝓞 F} (hD : H.det = ι D) {d v k : ℕ}
    (hDd : D ∉ 𝔭 ^ (d + 1)) (hn : n ∉ 𝔭 ^ (v + 1)) (hk : d + v + 1 ≤ k) :
    nkM 𝔭 (k + 1) H n * Ideal.absNorm 𝔭 = Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) * nkM 𝔭 k H n := by sorry
