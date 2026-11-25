-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G2_disc_equiv
-- name    : Formalism.L2.SG.Pf.G2.disc_equiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:48:34.318986+00:00
-- url     : https://prove2.me/theorems/d539ebec-a840-4701-9c9e-c876b4af2a0b
-- title:
--   G2: disc equiv
-- statement:
--   The G2 construction uses the disc equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscEquiv.lean#L52-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscEquiv.lean#L52-L89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFLeSpanK
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscEquiv
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G2
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
  {n : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F}

theorem Formalism.L2.SG.Pf.G2.disc_equiv (hF : IsFixF K F) (h𝔭 : 𝔭.IsMaximal) (hL : IsLatIn X L) (hbX : ∀ i, b i ∈ X)
    (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
    (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0) :
    Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] ∀ i : Fin n, 𝓞 K ⧸ extP K 𝔭 ^ vF 𝔭 (a i)) := by sorry
