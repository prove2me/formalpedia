-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_mem_pow_sub
-- name    : Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.mem_pow_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:08.263951+00:00
-- url     : https://prove2.me/theorems/17911619-3e17-48a2-9923-e298755b160b
-- title:
--   Extended Prime Ideals: mem pow sub
-- statement:
--   The Extended Prime Ideals construction uses the mem pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscrIdealLeIff.lean#L37-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscrIdealLeIff.lean#L37-L59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscrIdealLeIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.mem_pow_sub {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {s n : 𝓞 F} {k v : ℕ}
    (hn : n ∈ 𝔭 ^ v) (hn' : n ∉ 𝔭 ^ (v + 1)) (h : s * n ∈ 𝔭 ^ k) : s ∈ 𝔭 ^ (k - v) := by sorry
