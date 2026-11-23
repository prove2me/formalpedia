-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_iInf_locF
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:50:55.349364+00:00
-- url     : https://prove2.me/theorems/d08f012d-83b4-48f2-8a05-c8d58cece656
-- title:
--   Loc F: i Inf loc F
-- statement:
--   The Loc F construction uses the i Inf loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L54-L73

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_TraceReal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem Formalism.HermitianLattices.Ext.L3.LocF.iInf_locF (L : Submodule (𝓞 K) W) :
    (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 L) = L := by sorry
