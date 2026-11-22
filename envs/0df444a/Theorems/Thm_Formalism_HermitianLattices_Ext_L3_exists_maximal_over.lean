-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_maximal_over
-- name    : Formalism.HermitianLattices.Ext.L3.exists_maximal_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:23.167674+00:00
-- url     : https://prove2.me/theorems/c4ddfa2b-3280-40f3-ac66-3650f9ce192e
-- title:
--   L3: exists maximal over
-- statement:
--   The L3 construction uses the exists maximal over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L134-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L134-L148

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

theorem Formalism.HermitianLattices.Ext.L3.exists_maximal_over (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by sorry
