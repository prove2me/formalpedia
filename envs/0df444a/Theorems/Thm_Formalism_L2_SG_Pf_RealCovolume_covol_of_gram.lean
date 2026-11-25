-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RealCovolume_covol_of_gram
-- name    : Formalism.L2.SG.Pf.RealCovolume.covol_of_gram
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:29.109702+00:00
-- url     : https://prove2.me/theorems/e03ae392-4b57-4e8d-a15e-9404fadce896
-- title:
--   Real Covolume: covol of gram
-- statement:
--   The Real Covolume construction uses the covol of gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L102-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/RealCovolume.lean#L102-L208

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_RealCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RealCovolume
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem Formalism.L2.SG.Pf.RealCovolume.covol_of_gram {N : ℕ} (w : Fin N → (ι → κ → ℂ)) (g : κ → ℝ) (hg : ∀ c, g c ≠ 0)
    (hN : Fintype.card (ι × κ × Fin 2) = N)
    (hdet : (Matrix.of fun i j => Qf g (w i) (w j)).det ≠ 0) :
    Countable (AddSubgroup.closure (Set.range w)) ∧
    (∃ F : Set (ι → κ → ℂ), MeasurableSet F ∧
      ∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) ∧
    ∀ F : Set (ι → κ → ℂ), MeasurableSet F →
      (∀ v, ∃! a : AddSubgroup.closure (Set.range w), (a : ι → κ → ℂ) + v ∈ F) →
        volume F = ENNReal.ofReal (√|(Matrix.of fun i j => Qf g (w i) (w j)).det| / ∏ i : ι, ∏ c : κ, |g c|) := by sorry
