-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_interval_iter
-- name    : Formalism.FourierDecayAlt.P.Markov.interval_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:22.952387+00:00
-- url     : https://prove2.me/theorems/5d536afa-16e8-437b-b175-74ce5bb3f0d1
-- title:
--   Markov: interval iter
-- statement:
--   The Markov construction uses the interval iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L352-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L352-L364

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

theorem Formalism.FourierDecayAlt.P.Markov.interval_iter (hA : Formalism.FourierDecayAlt.E.AMarkov) (d : ℕ) (t₀ L : ℝ) (hL : 0 < L) (q : ℕ) :
    ∀ (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → (∀ t ∈ Set.Icc t₀ (t₀ + L), |P.eval t| ≤ M) →
    ∀ t ∈ Set.Icc t₀ (t₀ + L), |(derivative^[q] P).eval t| ≤ (2 * (d : ℝ) ^ 2 / L) ^ q * M := by sorry
