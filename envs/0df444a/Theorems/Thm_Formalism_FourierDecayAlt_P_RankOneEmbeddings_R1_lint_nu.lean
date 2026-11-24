-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_lint_nu
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.lint_nu
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:21:52.008508+00:00
-- url     : https://prove2.me/theorems/e583d612-c35c-472a-98b8-61a2abeaa7ff
-- title:
--   R1: lint nu
-- statement:
--   The R1 construction uses the lint nu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L417-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L417-L426

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1.lint_nu {s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hs : MeasSec s) (z z' : Vc k r)
    (μW μW' : Measure (Mt k r)) [SFinite μW] [SFinite μW'] (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ m, f m ∂(((wd k r z z').prod (μW.prod μW')).map (Phi s)) =
      ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) *
        ∫⁻ p : Mt k r × Mt k r, f (Phi s (ζ, p)) ∂(μW.prod μW') := by sorry
