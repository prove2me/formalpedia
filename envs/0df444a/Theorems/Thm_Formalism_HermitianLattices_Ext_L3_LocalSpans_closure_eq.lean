-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalSpans_closure_eq
-- name    : Formalism.HermitianLattices.Ext.L3.LocalSpans.closure_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:58.566182+00:00
-- url     : https://prove2.me/theorems/6cd6cc15-2d08-4b3d-bbaf-7a437803b2b2
-- title:
--   Local Spans: closure eq
-- statement:
--   The Local Spans construction uses the closure eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsBasisLocF.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsBasisLocF.lean#L17-L22

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalSpans
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LocalSpans.closure_eq (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] :
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} = sF K 𝔭 := by sorry
