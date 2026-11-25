-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G1_exists_basis_in
-- name    : Formalism.L2.SG.Pf.G1.exists_basis_in
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:41:46.343563+00:00
-- url     : https://prove2.me/theorems/64002a15-80f6-58c0-82b1-8576cea9a699
-- title:
--   G1: exists basis in
-- statement:
--   The G1 construction uses the exists basis in property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFMapSubtype.lean#L46-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/LocFMapSubtype.lean#L46-L84

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFMapSubtype
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [FiniteDimensional K V]

theorem Formalism.L2.SG.Pf.G1.exists_basis_in {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : Cnt.IsLatIn X L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ x : Fin (finrank K X) → V, (∀ i, x i ∈ L) ∧ LinearIndependent K x ∧
      Submodule.span K (Set.range x) = X ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range x)) = locF 𝔭 L := by sorry
