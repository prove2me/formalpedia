-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_natDegree_prodP
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.natDegree_prodP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:09:03.74975+00:00
-- url     : https://prove2.me/theorems/4c6fa59a-cfbd-43b5-b425-5fdab1e3daca
-- title:
--   Top Alg: nat Degree prod P
-- statement:
--   The Top Alg construction uses the nat Degree prod P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActAlg.lean#L35-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTRTopActAlg.lean#L35-L42

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

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.natDegree_prodP : ∀ {m : ℕ} (lin : Fin m → Prop) [DecidablePred lin] (B : Fin m → A),
    (prodP lin B).natDegree ≤ ∑ l, (if lin l then 1 else 0)
  := by sorry
