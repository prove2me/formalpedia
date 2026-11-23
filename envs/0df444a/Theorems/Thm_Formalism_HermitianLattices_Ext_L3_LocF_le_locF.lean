-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_le_locF
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.le_locF
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:56.654807+00:00
-- url     : https://prove2.me/theorems/bb857dfb-ab0e-4ed9-988a-246571670b55
-- title:
--   Loc F: le loc F
-- statement:
--   The Loc F construction uses the le loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L43-L44

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

theorem Formalism.HermitianLattices.Ext.L3.LocF.le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : L ≤ locF 𝔭 L := by sorry
