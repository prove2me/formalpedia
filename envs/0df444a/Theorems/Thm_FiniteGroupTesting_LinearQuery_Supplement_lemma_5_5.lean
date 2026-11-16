-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_5_5
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:25:06.596375+00:00
-- url     : https://prove2.me/theorems/2b6ef71c-2bf3-4abd-90a9-66d3457de697
-- title:
--   Lemma 5.5 — Soundness of the same Section 5 program
-- statement:
--   For every $n\ge2$ and $0<\epsilon<1/2$, if the arbitrary input operation is $\epsilon$-far from every group operation on the same labels, the complete Section 5 tester satisfies
--   $$\Pr[\mathrm{reject}]\ge2/3.$$
--   No spectral, inverse, cancellation, or group promise is imposed on a far input. Undefined locator values are failures. The finite distance grid ensures that $\epsilon$-farness also implies $\bar\epsilon$-farness when $\epsilon<n^{-2}$.
--
--   Differences from the source:
--   - encoding: labels [n]={1,...,n} → Fin n with zero representing paper label 1; reason: bijective relabelling preserves all tables, distances and query policies
--   - encoding: sufficient absolute constants in Sections 4–5 → fixed c_D=1/500, n_0=1500, gamma=1/10000, C_L=100, C_A=2000000, C_P=1000 and globally chosen expansion/fallback parameters; reason: these instantiate the displayed proof estimates uniformly; the predicates selecting numeric constants assume no existence or correctness, and the existing base theorems supply their witnesses
--   - encoding: candidate filters and possible early offline rejection before later trials → offline conjunction checked at the final decision, after shared action and product records are sampled; reason: this preserves every acceptance probability and the stated worst-case budget; it accesses the input only through the same visible oracle queries
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 34, Lemma 5.5

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_5_5 (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (hεhalf : ε < 1/2) (op : Table n) (hfar : Far ε op) :
    (2/3 : ℝ) ≤ OracleRun.probability op (· = false) (sublinearTester n ε) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
