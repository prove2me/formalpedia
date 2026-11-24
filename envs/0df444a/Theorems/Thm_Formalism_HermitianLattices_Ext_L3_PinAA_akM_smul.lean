-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinAA_akM_smul
-- name    : Formalism.HermitianLattices.Ext.L3.PinAA.akM_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:57.158281+00:00
-- url     : https://prove2.me/theorems/cfd1da18-574d-4b48-b652-6379fc19eced
-- title:
--   Pin AA: ak M smul
-- statement:
--   The Pin AA construction uses the ak M smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L168-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulEqZeroIff.lean#L168-L207

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
variable {κ : Type} [Fintype κ] [DecidableEq κ] [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.PinAA.akM_smul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {c : 𝓞 F}
    (hc : c ≠ 0) {k : ℕ} (hk : vF 𝔭 c ≤ k) (H : Matrix κ κ (𝓞 K)) :
    Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ k) //
        Xᴴ * (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) * X =
          (ι c • H).map (Ideal.Quotient.mk (extP K 𝔭 ^ k))} =
      Ideal.absNorm 𝔭 ^ (2 * vF 𝔭 c * Fintype.card κ ^ 2) *
        Nat.card {X : Matrix κ κ (𝓞 K ⧸ extP K 𝔭 ^ (k - vF 𝔭 c)) //
          Xᴴ * H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c))) * X =
            H.map (Ideal.Quotient.mk (extP K 𝔭 ^ (k - vF 𝔭 c)))} := by sorry
