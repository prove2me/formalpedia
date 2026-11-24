-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_mul_eq_zero_iff
-- name    : Formalism.HermitianLattices.Ext.L3.PinAA.mul_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:02.163198+00:00
-- url     : https://prove2.me/theorems/949579f8-5189-462b-b598-cddbf461074d
-- title:
--   Pin AA: mul eq zero iff
-- statement:
--   The Pin AA construction uses the mul eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L81-L86

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulEqZeroIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinAA
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans localValuationFiltration
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.PinAA.mul_eq_zero_iff {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F} (hc : c ≠ 0) {k : ℕ}
    (hk : vF 𝔭 c ≤ k) (z : 𝓞 K ⧸ extP K 𝔭 ^ k) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι c) * z = 0 ↔ rd K 𝔭 k (vF 𝔭 c) z = 0 := by sorry
