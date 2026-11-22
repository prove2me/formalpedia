-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_absNorm_conjIdeal
-- name    : Formalism.HermitianLattices.Ext.L3.absNorm_conjIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:20.754801+00:00
-- url     : https://prove2.me/theorems/55928e77-f6af-4f59-869c-0af9a994f0d2
-- title:
--   L3: abs Norm conj Ideal
-- statement:
--   The L3 construction uses the abs Norm conj Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSqAbsNormOfInert.lean#L78-L89

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.absNorm_conjIdeal (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (P : Ideal (𝓞 K)) :
    Ideal.absNorm (Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) = Ideal.absNorm P := by sorry
