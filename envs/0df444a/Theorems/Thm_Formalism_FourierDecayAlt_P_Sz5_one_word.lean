-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz5_one_word
-- name    : Formalism.FourierDecayAlt.P.Sz5.one_word
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:56.006815+00:00
-- url     : https://prove2.me/theorems/89084e41-ca42-471f-8098-a2e8499e31e7
-- title:
--   Sz5: one word
-- statement:
--   The Sz5 construction uses the one word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L850-L944
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CriticalThresholdLowerBound.lean#L850-L944

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CorollaryAOfPropositionA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CriticalThresholdLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz5
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz5.one_word (hPA : PropA) (hEa : EaSize) {ι : Type} [Fintype ι] (S : SizeData ι) (hOk : S.Ok)
    (hMR : S.MassRatios) (hLB : S.LBound) (hCC : S.ColumnCount) (hk : 2 ≤ S.k) (hg1 : 4 ≤ S.g1)
    (hg2 : 4 ≤ S.g2) (hds : ∀ w, 0 < S.dsig w) (C0 Gam : ℝ) (hC0 : 1 ≤ C0) (hGam : 0 < Gam)
    (hCh : S.ChoiceOfT C0 Gam) (hf2 : (S.f : ℝ) * (8 / 2 ^ S.k) ≤ Real.log 2) :
    |(S.f : ℝ) * ((S.k : ℝ) * Real.log S.T) - ∑ w, Real.log (S.TcritPow w) + 2 * Real.log Gam| ≤
      Real.log 2 + Real.log C0 := by sorry
