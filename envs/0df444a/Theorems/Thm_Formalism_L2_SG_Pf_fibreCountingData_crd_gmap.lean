-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_fibreCountingData_crd_gmap
-- name    : Formalism.L2.SG.Pf.fibreCountingData.crd_gmap
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:34.409533+00:00
-- url     : https://prove2.me/theorems/0613697e-ef35-5a5a-abfd-aa4a4845f707
-- title:
--   fibre Counting Data: crd gmap
-- statement:
--   The fibre Counting Data construction uses the crd gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/FibreCountingDataBis.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/FibreCountingDataBis.lean#L66-L69

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibreCountingDataBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha

theorem Formalism.L2.SG.Pf.fibreCountingData.crd_gmap (Y : Matrix (Fin m) (Fin m) (𝓞 K)) (x : V) (k : Fin m) :
    crd h b a (gmap h b a Y x) k = ∑ j, jK (Y k j) * crd h b a x j := by sorry
