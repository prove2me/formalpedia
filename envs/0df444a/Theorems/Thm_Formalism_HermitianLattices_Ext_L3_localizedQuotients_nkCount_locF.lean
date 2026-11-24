-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_nkCount_locF
-- name    : Formalism.HermitianLattices.Ext.L3.localizedQuotients.nkCount_locF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:30.656274+00:00
-- url     : https://prove2.me/theorems/83c97586-f75d-40fa-a57e-b9b02cde3090
-- title:
--   localized Quotients: nk Count loc F
-- statement:
--   The localized Quotients construction uses the nk Count loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L119-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L119-L146

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

theorem Formalism.HermitianLattices.Ext.L3.localizedQuotients.nkCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) :
    nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n := by sorry
