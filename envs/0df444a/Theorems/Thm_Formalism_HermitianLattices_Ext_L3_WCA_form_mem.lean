-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_form_mem
-- name    : Formalism.HermitianLattices.Ext.L3.WCA.form_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T09:48:11.96209+00:00
-- url     : https://prove2.me/theorems/1a3e152c-aa5b-492d-9eb8-fdd42e6df698
-- title:
--   WCA: form mem
-- statement:
--   The WCA construction uses the form mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InLZeroIff.lean#L126-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/InLZeroIff.lean#L126-L140

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AkCountEqRedCountMul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinitePrimesOfMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_mem

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCA
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem Formalism.HermitianLattices.Ext.L3.WCA.form_mem (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A)
    {i k : ℕ} {p q : V} (hp : p ∈ extP K 𝔭 ^ i • A) (hq : q ∈ extP K 𝔭 ^ k • A) :
    ∃ z ∈ extP K 𝔭 ^ (i + k), κ z = h p q := by sorry
