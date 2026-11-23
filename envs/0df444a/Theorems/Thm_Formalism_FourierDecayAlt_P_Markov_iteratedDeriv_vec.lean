-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_iteratedDeriv_vec
-- name    : Formalism.FourierDecayAlt.P.Markov.iteratedDeriv_vec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:22.65767+00:00
-- url     : https://prove2.me/theorems/f51ef9f0-2861-4991-b140-6aa276d1cc34
-- title:
--   Markov: iterated Deriv vec
-- statement:
--   The Markov construction uses the iterated Deriv vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L366-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L366-L382

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

theorem Formalism.FourierDecayAlt.P.Markov.iteratedDeriv_vec {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] {ι : Type}
    (S : Finset ι) (a : ι → H) (q : ℕ) : ∀ (P : ι → ℝ[X]),
    iteratedDeriv q (fun s : ℝ => ∑ k ∈ S, (P k).eval s • a k) =
      fun s : ℝ => ∑ k ∈ S, (derivative^[q] (P k)).eval s • a k := by sorry
