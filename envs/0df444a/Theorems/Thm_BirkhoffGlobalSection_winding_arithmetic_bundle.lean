-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_winding_arithmetic_bundle
-- name    : BirkhoffGlobalSection.winding_arithmetic_bundle
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-02T12:48:24.951226+00:00
-- url     : https://prove2.me/theorems/6e61ff3f-bab3-4bab-9568-dd657964809f
-- title:
--   Narrow winding-interval ceiling arithmetic and lower endpoint cases
-- statement:
--   For real numbers $a\le b$ with $b-a<1$, define $I(a,b)=\lceil a\rceil+\lceil b\rceil-1$. For every integer $k$,
--   $$2k+1\le I(a,b)\quad\Longleftrightarrow\quad k<a.$$
--   In particular $I(a,b)\ge3$ exactly when $a>1$. The other conjuncts give the noninteger and integer-crossing formulas, the distinct lower and upper integer-endpoint cases (including a singleton interval), and stability of this integer expression under sufficiently small common left shifts. These are arithmetic statements for supplied endpoints; they do not construct a winding interval or identify an index of a symplectic path.
--
--   **Formalization Note.** This theorem is the conjunction of 7 individually quantified results. Each conjunct retains the exact hypotheses of its local proof; the inventory is recorded with the publication artifacts.
-- source:
--   Original auxiliary results supporting the Birkhoff global-section formalization. Reeb and radial conventions: Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, arXiv:1105.2077v5, equations (1)-(2), Section 2.1.1 and the radial model on p. 2, https://arxiv.org/pdf/1105.2077 . Quaternionic conventions: Joung--van Koert, arXiv:2407.19159v3, Section 2.3. Supporting calculus and arithmetic: Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib. The auxiliary identities are original coordinate and calculus arguments; this is not a claimed formalization of the analytic prescribed-binding theorem. Local outcome documentation: notes/POSITIVE_TIME_CHANGE_WINDING.md.

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_BirkhoffGlobalSection_ContactVariationalInterfaces
open BirkhoffGlobalSection Set Filter SignType
open scoped ContDiff Topology
set_option linter.unusedVariables false

theorem BirkhoffGlobalSection.winding_arithmetic_bundle :
(∀ (a b : ℝ) (k : ℤ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    2 * k + 1 ≤ Int.ceil a + Int.ceil b - 1 ↔ (k : ℝ) < a) ∧
(∀ (a b : ℝ)
    (hab : a ≤ b) (hwidth : b - a < 1),
    (3 : ℤ) ≤ Int.ceil a + Int.ceil b - 1 ↔ 1 < a) ∧
(∀ (a b : ℝ) (k : ℤ)
    (ha : (k : ℝ) < a) (hab : a ≤ b) (hb : b < (k : ℝ) + 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k + 1) ∧
(∀ (a b : ℝ) (k : ℤ)
    (ha : a < (k : ℝ)) (hb : (k : ℝ) < b) (hwidth : b - a < 1),
    Int.ceil a + Int.ceil b - 1 = 2 * k) ∧
(∀ (a : ℝ) (k : ℤ)
    (ha : a ≤ (k : ℝ)) (hwidth : (k : ℝ) - a < 1),
    Int.ceil a + Int.ceil (k : ℝ) - 1 = 2 * k - 1) ∧
(∀ (b : ℝ) (k : ℤ)
    (hb : (k : ℝ) < b) (hwidth : b - (k : ℝ) < 1),
    Int.ceil (k : ℝ) + Int.ceil b - 1 = 2 * k) ∧
(∀ (a b : ℝ),
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      Int.ceil (a - ε) + Int.ceil (b - ε) - 1 = Int.ceil a + Int.ceil b - 1) := by sorry
