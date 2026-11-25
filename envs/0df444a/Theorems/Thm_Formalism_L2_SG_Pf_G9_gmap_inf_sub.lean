-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G9_gmap_inf_sub
-- name    : Formalism.L2.SG.Pf.G9.gmap_inf_sub
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:26:23.183348+00:00
-- url     : https://prove2.me/theorems/486f26a1-7bf6-5973-91af-19e2bc811bcc
-- title:
--   G9: gmap inf sub
-- statement:
--   The G9 construction uses the gmap inf sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegenerateOnOrthCompl.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegenerateOnOrthCompl.lean#L85-L99

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.G9.gmap_inf_sub {g : V ≃ₗ[K] V} (X : Submodule K V) (h1 : ∀ x ∈ X, g x ∈ X)
    (h2 : ∀ x ∈ X, g.symm x ∈ X) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ X.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ X.restrictScalars (𝓞 K) := by sorry
