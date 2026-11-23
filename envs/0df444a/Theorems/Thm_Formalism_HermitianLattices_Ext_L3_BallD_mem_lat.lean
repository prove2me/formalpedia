-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallD_mem_lat
-- name    : Formalism.HermitianLattices.Ext.L3.BallD.mem_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:08.589088+00:00
-- url     : https://prove2.me/theorems/f1481fef-3b1d-4ce8-ad82-baab3570c5ce
-- title:
--   Ball D: mem lat
-- statement:
--   The Ball D construction uses the mem lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MeasurableSetBallSet.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MeasurableSetBallSet.lean#L50-L51

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DiscreteTopologyOfZsmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VolumeNormSqLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FundamentalDomainPiBasis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthBasisMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MeasurableSetBallSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding MeasureTheory Module Pointwise
open scoped Classical
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallD
open BallB BallC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BallD.mem_lat {b : Basis (Fin (finrank K V)) K V} {L : Submodule (𝓞 K) V}
    {y : Fin (finrank K V) → mixedSpace K} : y ∈ lat b L ↔ ∃ x ∈ L, emb b x = y := by sorry
