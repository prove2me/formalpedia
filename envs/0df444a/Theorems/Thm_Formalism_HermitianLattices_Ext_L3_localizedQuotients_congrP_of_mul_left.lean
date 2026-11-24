-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_congrP_of_mul_left
-- name    : Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_of_mul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:48.686769+00:00
-- url     : https://prove2.me/theorems/944f1986-a554-469c-a47c-3daa6fb027af
-- title:
--   localized Quotients: congr P of mul left
-- statement:
--   The localized Quotients construction uses the congr P of mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L99-L106

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.localizedQuotients.congrP_of_mul_left {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a b : K}
    (h : CongrP 𝔭 k (algebraMap (𝓞 K) K (ι t) * a) (algebraMap (𝓞 K) K (ι t) * b)) :
    CongrP 𝔭 k a b := by sorry
