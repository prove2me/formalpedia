-- Prove2me | solution 1 for diophantine_quintuple_b_gt_3a
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T10:49:30.486926+00:00
-- url     : https://prove2.me/submissions/f00c1519-b94e-4d8d-8400-e9f8e1c58ba1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Conditional reduction for `diophantine_quintuple_b_gt_3a`
(Lemma `lem:b3a` in 1610.04020v2.tex: an ordered Diophantine quintuple
satisfies `b > 3a`, i.e. `3 * f 0 < f 1`).

Source proof (verified against the cited paper itself: Cipu–Fujita, "Bounds
for Diophantine quintuples", Glasnik Mat. 50(1) (2015), 25–34,
DOI 10.3336/gm.50.1.03; Theorem 1.1, proof pp. 31–32). The paper states
Theorem 1.1 as non-existence: no quintuple has `b ≤ 3a`. Its machinery:
  * the Pell system (3.1)–(3.2) from eliminating `d`, whose solutions are
    common terms `z = v_{2m} = w_{2n}` (`m ≥ 3`, `n ≥ 2`) of two recurrent
    sequences ([12]; the index bounds need the fifth element, so the
    argument is genuinely quintuple-level — indeed it is FALSE below that
    level: `{1,3,8,120}` is a quadruple with `b = 3a`, and `{3,8,21}` a
    triple with `b < 3a`);
  * an upper bound for the index `n` (Lemmas 3.1–3.3) from an improved
    Rickert-type simultaneous-approximation theorem (Theorem 2.2:
    hypergeometric method after Bennett [3], Schoenfeld [22] prime bounds,
    a PARI computation) applied with `N = abd`;
  * a lower bound `m > 0.5·b^{−1/2}·d^{1/2}` (Lemma 3.4 = Cipu [6,
    Lemma 2.4]);
  * absolute lower bounds for `b` (Lemma 2.1: Baker–Davenport reduction
    [13]: `b > 21000` if `b < 2a`, `b > 130000` if `2a ≤ b ≤ 8a`),
    contradicting the derived upper bounds (`b < 200`, resp. `b < 97000`).
None of this machinery (hypergeometric approximations, Chebyshev prime
bounds, Baker–Davenport reduction computations) is available elementarily,
so a direct Lean proof is out of reach; the neighboring-square method of
`work/PiIrregularDirect.lean` does not transfer either (it refutes a regular
value of the top element via `(d−a−b)² = c·e+(2r)²`, while here only `a,b`
are constrained).

Architecture. Mirror the source proof's own split on the ratio `b/a`
(NOT an Euler/non-Euler split — the source never splits on Euler for
Theorem 1.1). The two scratch children under `work/PiB3aWorkspace/`
conclude `False` (non-existence over complementary ratio intervals), each
isolating one half of the source computation with its own constants:
  * `diophantine_quintuple_not_b_lt_2a` — first case, `b < 2a → False`
    (`21000` versus `b < 200`; estimates via Lemma 3.5 and [14]);
  * `diophantine_quintuple_not_b_le_3a_of_2a_le` — second case,
    `2a ≤ b ≤ 3a → False` (`130000` versus `b < 97000`; AM–GM step).
The parent assembly is an elementary ratio trichotomy (`omega`): given
`b < 2a`, the first child closes the goal ex falso; given
`2a ≤ b ≤ 3a`, the second child does; otherwise `3a < b` holds directly.
Each child is reusable on its own: the first is exactly what kills the
`b < 2a` alternative of the Fujita–Miyazaki criterion wherever `b > 3a` is
currently invoked. No tracked module is imported (in particular neither the
parent target itself nor the `acb` upper-bound reduction that depends on
this lemma — avoiding circularity), and no Euler-triple elimination is used
(mission `degree_zero` is itself an open gap whose source proof depends on
`b > 3a` via `lem:min_bcd`, so it would be circular here). This file is
fully proved and declares no new foundational assumptions.
-/
import Definitions.Def_diophantine_descent
import Theorems.Thm_diophantine_quintuple_not_b_lt_2a
import Theorems.Thm_diophantine_quintuple_not_b_le_3a_of_2a_le
set_option autoImplicit false
open DiophantineDescent

theorem solution (f : Fin 5 → Nat)
    (hq : Quintuple f)
    (ho : Ordered f) :
    3 * f 0 < f 1 := by
  by_cases h1 : f 1 < 2 * f 0
  · exact False.elim (diophantine_quintuple_not_b_lt_2a f hq ho h1)
  · by_cases h2 : f 1 ≤ 3 * f 0
    · have h1' : 2 * f 0 ≤ f 1 := by omega
      exact False.elim
        (diophantine_quintuple_not_b_le_3a_of_2a_le f hq ho h1' h2)
    · omega
