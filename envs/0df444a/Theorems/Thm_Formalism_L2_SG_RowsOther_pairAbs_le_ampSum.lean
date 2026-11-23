-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_pairAbs_le_ampSum
-- name    : Formalism.L2.SG.RowsOther.pairAbs_le_ampSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:26.796208+00:00
-- url     : https://prove2.me/theorems/0a11c311-41f8-4f02-8ba6-dfb3efccaa35
-- title:
--   Rows Other: pair Abs le amp Sum
-- statement:
--   The Rows Other construction uses the pair Abs le amp Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L89-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L89-L103

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

theorem Formalism.L2.SG.RowsOther.pairAbs_le_ampSum (hG : 0 ≤ X.Gam1) (Q : Set (τ × τ))
    (hs : Summable (Q.indicator (fun p : τ × τ => ‖X.vec p.1‖ * ‖X.vec p.2‖))) :
    X.pairAbs Q ≤ X.Gam1 * ampSum X Q := by sorry
