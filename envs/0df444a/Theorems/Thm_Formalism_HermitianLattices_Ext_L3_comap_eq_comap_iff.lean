-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_comap_eq_comap_iff
-- name    : Formalism.HermitianLattices.Ext.L3.comap_eq_comap_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:13:21.981807+00:00
-- url     : https://prove2.me/theorems/72b294c0-2887-4105-be56-6c2a730c2e74
-- title:
--   L3: comap eq comap iff
-- statement:
--   The L3 construction uses the comap eq comap iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L128-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L128-L132

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_eq_comap_iff

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

theorem Formalism.HermitianLattices.Ext.L3.comap_eq_comap_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P Q : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hQ : Q.IsMaximal) :
    P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) ↔ Q = P ∨ Q = Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by sorry
