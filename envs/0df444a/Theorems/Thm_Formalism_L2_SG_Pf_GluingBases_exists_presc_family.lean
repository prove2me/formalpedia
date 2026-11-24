-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_exists_presc_family
-- name    : Formalism.L2.SG.Pf.GluingBases.exists_presc_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:26.420489+00:00
-- url     : https://prove2.me/theorems/8bfdc566-97c2-4975-8cbd-9ccaa9cdea8b
-- title:
--   Gluing Bases: exists presc family
-- statement:
--   The Gluing Bases construction uses the exists presc family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L41-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L41-L122

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram]

theorem Formalism.L2.SG.Pf.GluingBases.exists_presc_family (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) [FiniteDimensional K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ x y, star (h x y) = h y x)
    (hpos : ∀ x, x ≠ 0 → TotPos (h x x)) :
    ∀ k : ℕ, k + 1 ≤ finrank K V → ∀ t : Fin (k + 1) → K, (∀ i, star (t i) = t i) →
      (∀ i, TotPos (t i)) →
      ∃ v : Fin (k + 1) → V, (∀ i j, i ≠ j → h (v i) (v j) = 0) ∧
        (∀ i, i ≠ Fin.last k → h (v i) (v i) = t i) ∧ v (Fin.last k) ≠ 0 := by sorry
