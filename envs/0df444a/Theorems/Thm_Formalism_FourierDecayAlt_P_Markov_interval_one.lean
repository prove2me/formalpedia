-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_interval_one
-- name    : Formalism.FourierDecayAlt.P.Markov.interval_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:27.775477+00:00
-- url     : https://prove2.me/theorems/06d69655-29b5-4774-8bd6-4e3ca38d77c9
-- title:
--   Markov: interval one
-- statement:
--   The Markov construction uses the interval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L313-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L313-L350

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial

theorem Formalism.FourierDecayAlt.P.Markov.interval_one (hA : Formalism.FourierDecayAlt.E.AMarkov) (P : ℝ[X]) (d : ℕ) (t₀ L M : ℝ) (hL : 0 < L)
    (hd : P.natDegree ≤ d) (hP : ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) :
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |P.derivative.eval t| ≤ (2 * (d : ℝ) ^ 2 / L) * M := by sorry
