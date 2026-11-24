-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_mem_extP_of_mul
-- name    : Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.mem_extP_of_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:53.182967+00:00
-- url     : https://prove2.me/theorems/61450d05-28b5-44af-97e0-566ee1183bc4
-- title:
--   Extended Prime Ideals: mem ext P of mul
-- statement:
--   The Extended Prime Ideals construction uses the mem ext P of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscrIdealLeIff.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/DiscrIdealLeIff.lean#L17-L25

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

theorem Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals.mem_extP_of_mul {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ∉ 𝔭) {k : ℕ}
    {z : 𝓞 K} (hz : algebraMap (𝓞 F) (𝓞 K) t * z ∈ extP K 𝔭 ^ k) : z ∈ extP K 𝔭 ^ k := by sorry
