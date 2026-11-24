-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_push_calc
-- name    : Formalism.FourierDecayAlt.P.TwoByOneBlock.push_calc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:50.269627+00:00
-- url     : https://prove2.me/theorems/5e69cc8e-aff9-4975-ba79-a5c407c155f9
-- title:
--   Two By One Block: push calc
-- statement:
--   The Two By One Block construction uses the push calc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1109-L1157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean#L1109-L1157

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open Set
open scoped Pointwise

theorem Formalism.FourierDecayAlt.P.TwoByOneBlock.push_calc (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      (∫⁻ u : Fin (k + 1) → ℂ in {u | 0 < Nq k u ∧ Nq k u ≤ T'},
          φ (((-(√T * √(T' / Nq k u)) : ℝ) : ℂ) * u (Fin.last k))) =
        c * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * φ ζ := by sorry
