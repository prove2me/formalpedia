-- Prove2me | Theorems.Thm_APFPaper5_K3_exists_noncommuting_of_rangesOver
-- name    : APFPaper5.K3.exists_noncommuting_of_rangesOver
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:21:55.519018+00:00
-- url     : https://prove2.me/theorems/a1141363-fdbf-4ac7-84be-75bafbce6067
-- title:
--   Interval-valued sandwich numbers force noncommuting idempotent marks under explicit algebraic hypotheses
-- statement:
--   Let A be a real algebra and p,q:S→A be idempotent at every state, with p always nonzero. Assume p(s)q(s)p(s)=rel(s)•p(s), and assume rel attains every value of a nondegenerate interval. Then p(s) and q(s) fail to commute at some state. The supplied algebra, idempotence, nonzero condition, sandwich relation and interval coverage are all hypotheses; the theorem does not construct an interface realizing them. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_continuity_consequences.lean', 'line': 66, 'declaration': 'APFPaper5.K3.exists_noncommuting_of_rangesOver', 'sha256': '4fe8ac46703b4872830c2a80c2c5f4b7092d9fc3d9375ceb62e57001b7a01493'}]

import Definitions.Def_APFPaper5_K3_Continuity
import Theorems.Thm_APFPaper1_RecordBook_pair_number_zero_or_one_of_commute
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u uA
variable {S : Type u}

theorem APFPaper5.K3.exists_noncommuting_of_rangesOver {A : Type uA} [Ring A] [Algebra ℝ A]
    (p q : S → A) (rel : S → ℝ) (lo hi : ℝ)
    (hp : ∀ s : S, p s * p s = p s) (hq : ∀ s : S, q s * q s = q s) (hp0 : ∀ s : S, p s ≠ 0)
    (hrel : ∀ s : S, p s * q s * p s = rel s • p s)
    (h : RangesOverInterval rel lo hi) : ∃ s : S, p s * q s ≠ q s * p s := by sorry
