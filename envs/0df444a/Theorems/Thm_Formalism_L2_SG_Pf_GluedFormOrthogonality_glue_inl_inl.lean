-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluedFormOrthogonality_glue_inl_inl
-- name    : Formalism.L2.SG.Pf.GluedFormOrthogonality.glue_inl_inl
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:48.417799+00:00
-- url     : https://prove2.me/theorems/a899875c-5d55-55b5-bc6a-988b9c189c63
-- title:
--   Glued Form Orthogonality: glue inl inl
-- statement:
--   The Glued Form Orthogonality construction uses the glue inl inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/GlueInlInl.lean#L25-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueLocalOfFam
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueInlInl
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluedFormOrthogonality
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.SG.Pf.GluedFormOrthogonality.glue_inl_inl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by sorry
