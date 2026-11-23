-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_T_eq_nodal
-- name    : Formalism.FourierDecayAlt.P.Markov.T_eq_nodal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:36.021494+00:00
-- url     : https://prove2.me/theorems/73371a0b-f514-4e6b-ab53-26137572d43b
-- title:
--   Markov: T eq nodal
-- statement:
--   The Markov construction uses the T eq nodal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L58-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L58-L74

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

theorem Formalism.FourierDecayAlt.P.Markov.T_eq_nodal (n : ℕ) (hn : n ≠ 0) :
    Chebyshev.T ℝ n =
      C ((2 : ℝ) ^ (n - 1)) * Lagrange.nodal (Finset.range n) (fun k => cos (th n k)) := by sorry
