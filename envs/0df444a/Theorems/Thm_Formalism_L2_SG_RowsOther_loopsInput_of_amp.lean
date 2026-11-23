-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_loopsInput_of_amp
-- name    : Formalism.L2.SG.RowsOther.loopsInput_of_amp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:18.031809+00:00
-- url     : https://prove2.me/theorems/669c71e3-1b0e-4ecd-a783-39452aa35f97
-- title:
--   Rows Other: loops Input of amp
-- statement:
--   The Rows Other construction uses the loops Input of amp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L114-L116

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
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)

theorem Formalism.L2.SG.RowsOther.loopsInput_of_amp (hG : 0 ≤ X.Gam1) (A C : ℝ) (k r f : ℕ) (b g v Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ)
    (h : LoopsAmp X A C k r f b g v Gam Xi dd) : PB.LoopsInput X A C k r f b g v Gam Xi dd := by sorry
