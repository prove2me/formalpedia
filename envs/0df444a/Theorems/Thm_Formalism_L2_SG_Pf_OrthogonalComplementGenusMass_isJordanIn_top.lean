-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_OrthogonalComplementGenusMass_isJordanIn_top
-- name    : Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.isJordanIn_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:25:32.476636+00:00
-- url     : https://prove2.me/theorems/c5baa534-e761-563c-80ce-7c8c1e64f14a
-- title:
--   Orthogonal Complement Genus Mass: is Jordan In top
-- statement:
--   The Orthogonal Complement Genus Mass construction uses the is Jordan In top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L122-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExtensionIdentityOfMemCompl.lean#L122-L141

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExtensionIdentityOfMemCompl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.OrthogonalComplementGenusMass.isJordanIn_top {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) ↥X}
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (H : IsJordanIn h X (push X L) 𝔭 b a) :
    IsJordanIn (formOn h X) ⊤ L 𝔭 (fun i => ⟨b (Fin.cast (finrank_top K ↥X) i), H.1 _⟩)
      (fun i => a (Fin.cast (finrank_top K ↥X) i)) := by sorry
