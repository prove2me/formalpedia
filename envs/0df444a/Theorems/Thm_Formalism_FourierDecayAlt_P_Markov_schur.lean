-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_schur
-- name    : Formalism.FourierDecayAlt.P.Markov.schur
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:18.29268+00:00
-- url     : https://prove2.me/theorems/d5cc0c6a-a4c1-4731-b8ad-f95aa34cfb93
-- title:
--   Markov: schur
-- statement:
--   The Markov construction uses the schur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L96-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L96-L142

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
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.schur (n : ℕ) (hn : n ≠ 0) (r : ℝ[X]) (hr : r.degree < n) (c : ℝ)
    (hC : ∀ k < n, |sin (th n k) * r.eval (cos (th n k))| ≤ c)
    (y : ℝ) (hy : ∀ k < n, cos (th n k) < y) (hy1 : y ≤ 1) : |r.eval y| ≤ n * c := by sorry
