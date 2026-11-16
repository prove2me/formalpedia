-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_5_4
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:24:27.923713+00:00
-- url     : https://prove2.me/theorems/63dd150e-16e5-44d0-bd0f-d73ed436b894
-- title:
--   Lemma 5.4 — Completeness of the Section 5 program
-- statement:
--   For every $n\ge2$, $0<\epsilon<1/2$, and genuine input group table, the complete Section 5 tester satisfies
--   $$\Pr[\mathrm{accept}]\ge2/3.$$
--   The statement names the actual dictionary-and-locator tester, with its finite budgets, shared samples and immutable linear fallback, rather than an assumed-correct evaluator. Its numerical parameter choices are those listed in the tester definition.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - encoding: sufficient absolute constants in Sections 4–5 → fixed c_D=1/500, n_0=1500, gamma=1/10000, C_L=100, C_A=2000000, C_P=1000 and globally chosen expansion/fallback parameters; reason: these instantiate the displayed proof estimates uniformly; the predicates selecting numeric constants assume no existence or correctness, and the existing base theorems supply their witnesses
--   - encoding: candidate filters and possible early offline rejection before later trials → offline conjunction checked at the final decision, after shared action and product records are sampled; reason: this preserves every acceptance probability and the stated worst-case budget; it accesses the input only through the same visible oracle queries
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 34, Lemma 5.4

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_5_4 (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < 1/2) (op : Table n) (hop : IsGroupLaw op) :
    (2/3 : ℝ) ≤ OracleRun.probability op (· = true) (sublinearTester n ε) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
