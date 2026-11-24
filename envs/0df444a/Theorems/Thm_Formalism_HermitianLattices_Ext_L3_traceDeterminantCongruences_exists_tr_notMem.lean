-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_traceDeterminantCongruences_exists_tr_notMem
-- name    : Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_tr_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:41.067377+00:00
-- url     : https://prove2.me/theorems/f8dd3d15-fab0-4712-b977-92f77b4b4a56
-- title:
--   trace Determinant Congruences: exists tr not Mem
-- statement:
--   The trace Determinant Congruences construction uses the exists tr not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L39-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySeventh.lean#L39-L61

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
open idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences.exists_tr_notMem (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {N : ℕ} {z : 𝓞 K} (hz : z ∉ extP K 𝔭 ^ N) :
    ∃ b : 𝓞 K, trF hF (b * z) ∉ 𝔭 ^ N := by sorry
