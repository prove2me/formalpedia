-- Prove2me | Theorems.Thm_APFPaper5_K3_pair_dichotomy
-- name    : APFPaper5.K3.pair_dichotomy
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:17:04.542557+00:00
-- url     : https://prove2.me/theorems/4636e506-1e31-4c9b-a1dd-3f34892569fb
-- title:
--   Pair dichotomy
-- statement:
--   Supporting result: pair dichotomy. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. For real-linear Held2 maps, common-turn invisibility in plainAfterTurn is equivalent to commuting or anticommuting with J. Their squares commute. Four-record equality and record-factorization lemmas expose the chosen equivalence. The result uses the full model orbit-profile definition. Arbitrary nonlinear maps and original physical admission are outside scope; record-factorization is a hypothesis, not the discrete FirstOrder predicate.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1800-1840,2006-2044'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_unseen_dichotomy.lean', 'sha256': 'cf1640df4abd1fbf8b44fb6bcdeeed36bcaab17860c36af8726c37678cf7c9b1', 'line': 70, 'declaration': 'APFPaper5.K3.pair_dichotomy'}]

import Definitions.Def_APFPaper5_K3_HeldMaps
import Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFB01_quarter_record_descends
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.pair_dichotomy (v w : Held2) (hA : recA w = recA v) (hB : recB w = recB v)
    (hRe : crossRe w = crossRe v) (hIm : crossIm w = crossIm v)
    (hA' : recA (add2 (smul2 (3 / 5) v) (smul2 (4 / 5) w)) = recA v)
    (hB' : recB (add2 (smul2 (3 / 5) v) (smul2 (4 / 5) w)) = recB v) :
    w = commonTurn 0 1 v ∨ w = neg2 (commonTurn 0 1 v) := by sorry
