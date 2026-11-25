-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_coeff_all
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.coeff_all
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:18:47.214806+00:00
-- url     : https://prove2.me/theorems/78591a30-a5cf-43bd-8ae4-62bf291425d4
-- title:
--   Top Alg: coeff all
-- statement:
--   The Top Alg construction uses the coeff all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActAlg.lean#L56-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActAlg.lean#L56-L79

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.REAL
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.coeff_all : ∀ {m : ℕ} (B : Fin m → A),
    (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff m = 1 ∧
      (1 ≤ m → (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff (m - 1) = ∑ l, B l)
  := by sorry
