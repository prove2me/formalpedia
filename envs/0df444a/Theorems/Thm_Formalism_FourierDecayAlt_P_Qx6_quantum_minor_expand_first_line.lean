-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_quantum_minor_expand_first_line
-- name    : Formalism.FourierDecayAlt.P.Qx6.quantum_minor_expand_first_line
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:35:55.04499+00:00
-- url     : https://prove2.me/theorems/f51bb700-5948-414d-a13b-abc03597f923
-- title:
--   Qx6: quantum minor expand first line
-- statement:
--   The Qx6 construction uses the quantum minor expand first line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L285-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainRecursionFromSingleDescent.lean#L285-L291

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem Formalism.FourierDecayAlt.P.Qx6.quantum_minor_expand_first_line (hFR : ExpFirstRow) (hSk : QSkewRow) (hE : GlRel E) {t : ℕ} (f : Fin t → Fin n) (e : Fin n)
    (b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E (bS f e) b u = ∑ x : Fin (t + 1), ((-1 : ℤ) ^ (t + (x : ℕ))) •
      (Tm E (u - (t : ℂ)) e (b x) * qminor E f (b ∘ x.succAbove) u) := by sorry
