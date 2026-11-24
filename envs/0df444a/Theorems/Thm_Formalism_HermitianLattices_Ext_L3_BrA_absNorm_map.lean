-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_map
-- name    : Formalism.HermitianLattices.Ext.L3.BrA.absNorm_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:04.423974+00:00
-- url     : https://prove2.me/theorems/da5581ff-4ec7-47d7-9a99-1ae3bff534d6
-- title:
--   Br A: abs Norm map
-- statement:
--   The Br A construction uses the abs Norm map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FinrankRingOfIntegers.lean#L55-L57

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module IsDedekindDomain Function
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BrA.absNorm_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm I ^ 2 := by sorry
