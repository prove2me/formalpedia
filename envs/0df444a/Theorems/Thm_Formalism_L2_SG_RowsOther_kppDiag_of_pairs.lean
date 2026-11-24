-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_kppDiag_of_pairs
-- name    : Formalism.L2.SG.RowsOther.kppDiag_of_pairs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:27.27223+00:00
-- url     : https://prove2.me/theorems/9b9a2d0f-1ae4-4959-8b75-7a49fa8d171d
-- title:
--   Rows Other: kpp Diag of pairs
-- statement:
--   The Rows Other construction uses the kpp Diag of pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L35-L46

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

theorem Formalism.L2.SG.RowsOther.kppDiag_of_pairs [CompleteSpace H₁] (hP : PB.NormSqBoundOfEqualIota) (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit)
    (hSub : PB.SubFamily) (Pg du : ℝ) (k f : ℕ) (hPg : 0 ≤ Pg) (hAbs : X.AbsConv) (hO : X.RowOrth)
    (hC : X.CorankPos) (hN : X.NormExpansionOn X.degSet) (hG : X.GGBound Pg)
    (hB : PairsDeg X Pg du k f) : KppDiag X du k f := by sorry
