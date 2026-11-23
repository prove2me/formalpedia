-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_diag_of_abstract
-- name    : Formalism.L2.SG.RowsOther.diag_of_abstract
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:32.126069+00:00
-- url     : https://prove2.me/theorems/040294a4-4d38-40dd-b777-92ca478c2e6d
-- title:
--   Rows Other: diag of abstract
-- statement:
--   The Rows Other construction uses the diag of abstract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L72-L81

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

theorem Formalism.L2.SG.RowsOther.diag_of_abstract [CompleteSpace H₁] (hA : PB.PairBoundAbstract) (hP : PB.NormSqBoundOfEqualIota)
    (hE : PB.GramSumLeOfPosSemidef) (hS : PB.PairSplit) (hSub : PB.SubFamily) (one : H) (Pg A ε ε' dd : ℝ)
    (hPg : 0 ≤ Pg) (hdd : 0 ≤ dd) (hAbs : X.AbsConv)
    (hN : X.NormExpansionOn X.genSet ∧ X.NormExpansionOn X.ngSet) (hG : X.GGBound Pg)
    (hO : X.RowOrth) (hC : X.CorankPos) (hI : IdOne X one) (h1 : X.RowBig ε dd)
    (h2 : X.RowNotScalar ε dd) (h3 : X.RowMain A dd) (h4 : X.RowNG ε' dd) :
    DiagRow X one ((√(Pg * (A + 2 * ε)) + √(Pg * (ε + ε'))) ^ 2) dd := by sorry
