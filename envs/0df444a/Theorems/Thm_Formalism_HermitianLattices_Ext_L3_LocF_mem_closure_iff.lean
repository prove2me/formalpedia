-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_mem_closure_iff
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.mem_closure_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:47.483174+00:00
-- url     : https://prove2.me/theorems/c9c2ca9b-d98d-4c52-a3e0-303fcb817796
-- title:
--   Loc F: mem closure iff
-- statement:
--   The Loc F construction uses the mem closure iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AlgebraMapIntCastSmul.lean#L17-L30

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

theorem Formalism.HermitianLattices.Ext.L3.LocF.mem_closure_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (s : 𝓞 K) :
    s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} ↔
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by sorry
