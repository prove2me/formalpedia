-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_rowLoops_of_input
-- name    : Formalism.L2.SG.RowsOther.rowLoops_of_input
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:10.015774+00:00
-- url     : https://prove2.me/theorems/efaf6d59-88ad-41ed-a81f-0f4919922a65
-- title:
--   Rows Other: row Loops of input
-- statement:
--   The Rows Other construction uses the row Loops of input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L150-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L150-L164

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt

theorem Formalism.L2.SG.RowsOther.rowLoops_of_input (hL : PN.LoopCores) (hSub : PB.SubFamily) (C : ℝ) (hC : 1 ≤ C) :
    ∃ K₀ : ℝ, ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) (k r f : ℕ)
      (A b g v NT Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ), 1 ≤ A →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k (2 * r + 2) f b g v NT Gam →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k (2 * r + 2) f b v NT Xi →
      6 * Real.log (3 * A) ≤ (k : ℝ) * f * Real.log k → 0 ≤ dd → X.AbsConv →
      PB.LoopsInput X A C k r f b g v Gam Xi dd →
      X.RowBig (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd ∧
      X.RowNotScalar (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd := by sorry
