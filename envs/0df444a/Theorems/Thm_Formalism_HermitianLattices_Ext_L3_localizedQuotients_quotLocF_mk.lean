-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_quotLocF_mk
-- name    : Formalism.HermitianLattices.Ext.L3.localizedQuotients.quotLocF_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:36.91223+00:00
-- url     : https://prove2.me/theorems/11676c03-697d-45b3-bf8f-58d8e84490ed
-- title:
--   localized Quotients: quot Loc F mk
-- statement:
--   The localized Quotients construction uses the quot Loc F mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulOfMemSmulLocF.lean#L85-L87

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

theorem Formalism.HermitianLattices.Ext.L3.localizedQuotients.quotLocF_mk {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (L : Submodule (𝓞 K) V) (k : ℕ) (y : ↥L)
    (hy : (y : V) ∈ locF 𝔭 L) :
    quotLocF h𝔭 L k (Submodule.Quotient.mk y) = Submodule.Quotient.mk ⟨(y : V), hy⟩ := by sorry
