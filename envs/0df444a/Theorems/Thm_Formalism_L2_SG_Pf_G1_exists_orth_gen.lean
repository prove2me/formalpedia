-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_G1_exists_orth_gen
-- name    : Formalism.L2.SG.Pf.G1.exists_orth_gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:52.00666+00:00
-- url     : https://prove2.me/theorems/c0d0c35b-2cd4-4512-831c-22c174ecede4
-- title:
--   G1: exists orth gen
-- statement:
--   The G1 construction uses the exists orth gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L30-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsOrthGen.lean#L30-L169

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTuple
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsOrthGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G1
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K}

theorem Formalism.L2.SG.Pf.G1.exists_orth_gen (hS : IsHermSemilocal S) (hπ : IsUnif S π) :
    ∀ (n N : ℕ) (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → ∀ x : Fin n → V, (∀ i j, h (x i) (x j) ∈ S) →
      (U0.gram h x).det * π⁻¹ ^ N ∉ S →
      ∃ y : Fin n → V, (∀ i j, i ≠ j → h (y i) (y j) = 0) ∧ spanS S y = spanS S x := by sorry
