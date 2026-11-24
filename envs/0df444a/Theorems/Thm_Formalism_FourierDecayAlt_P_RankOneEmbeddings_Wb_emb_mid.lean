-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mid
-- name    : Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_mid
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:03:31.108007+00:00
-- url     : https://prove2.me/theorems/caeb5903-4041-4458-91f0-49a324f199de
-- title:
--   Wb: emb mid
-- statement:
--   The Wb construction uses the emb mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L37-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean#L37-L40

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb.emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ ⟨q.val - r, by have := hq; omega⟩ ⟨j.val - r, by have := hj; omega⟩ := by sorry
