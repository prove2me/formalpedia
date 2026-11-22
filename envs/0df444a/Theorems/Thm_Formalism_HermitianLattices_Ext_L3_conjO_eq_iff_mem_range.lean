-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_eq_iff_mem_range
-- name    : Formalism.HermitianLattices.Ext.L3.conjO_eq_iff_mem_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:39:40.242124+00:00
-- url     : https://prove2.me/theorems/a96b7d4a-11c4-4846-89e8-656ebea5e88f
-- title:
--   L3: conj O eq iff mem range
-- statement:
--   The L3 construction uses the conj O eq iff mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L105-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L105-L126

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.conjO_eq_iff_mem_range (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by sorry
