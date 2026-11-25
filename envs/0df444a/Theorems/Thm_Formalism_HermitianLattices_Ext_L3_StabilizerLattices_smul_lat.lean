-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_smul_lat
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.smul_lat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:30.527616+00:00
-- url     : https://prove2.me/theorems/a3de9d42-9b63-4e28-8948-3bd89511f015
-- title:
--   Stabilizer Lattices: smul lat
-- statement:
--   The Stabilizer Lattices construction uses the smul lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSmulMem.lean#L48-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsSmulMem.lean#L48-L48

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsVecOfHermRep
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Lemmata_GeneralBFactSecondForm_Imports
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
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
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.smul_lat (g : Formalism.HermitianLatticesTheory.isom h) (Λ : Submodule (𝓞 K) V) : g • Λ = Formalism.HermitianLatticesTheory.gmap g.1 Λ := by sorry
