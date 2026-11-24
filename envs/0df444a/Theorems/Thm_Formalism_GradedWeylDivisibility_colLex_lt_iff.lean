-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_colLex_lt_iff
-- name    : Formalism.GradedWeylDivisibility.colLex_lt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:52.992792+00:00
-- url     : https://prove2.me/theorems/cefb1e27-1966-42b5-931a-4032ccd35212
-- title:
--   Graded Weyl Divisibility: col Lex lt iff
-- statement:
--   The Graded Weyl Divisibility construction uses the col Lex lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementC.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/StatementC.lean#L24-L25

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder

theorem Formalism.GradedWeylDivisibility.colLex_lt_iff {r n : ℕ} {c d : Fin r × Fin n →₀ ℕ} :
    c ≺[colLex r n] d ↔ toLex (Finsupp.domCongr (cmIdx r n) c) < toLex (Finsupp.domCongr (cmIdx r n) d) := by sorry
