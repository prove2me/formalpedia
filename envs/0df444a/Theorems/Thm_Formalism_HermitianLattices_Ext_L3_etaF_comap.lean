-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_etaF_comap
-- name    : Formalism.HermitianLattices.Ext.L3.etaF_comap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:45.366099+00:00
-- url     : https://prove2.me/theorems/db5e5301-19a7-45c7-ad55-a232b7cfcba8
-- title:
--   L3: eta F comap
-- statement:
--   The L3 construction uses the eta F comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L165-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L165-L174

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

theorem Formalism.HermitianLattices.Ext.L3.etaF_comap (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    etaF K F (P.comap (algebraMap (𝓞 F) (𝓞 K))) = if Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P then -1 else 1 := by sorry
