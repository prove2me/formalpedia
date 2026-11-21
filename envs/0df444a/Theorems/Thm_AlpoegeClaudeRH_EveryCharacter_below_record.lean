-- Prove2me | Theorems.Thm_AlpoegeClaudeRH_EveryCharacter_below_record
-- name    : AlpoegeClaudeRH.EveryCharacter_below_record
-- status  : Open
-- author  : @mwm
-- created : 2026-11-21T03:01:43.587904+00:00
-- url     : https://prove2.me/theorems/bc62e10f-cec3-49f8-8815-75ea1108db29
-- title:
--   Nonvanishing of Dirichlet L-functions below the verified zero-free boundary
-- statement:
--   Let $q \ge 1$ be an integer, let $\chi$ be a Dirichlet character modulo $q$ valued in $\mathbb{C}$, and let $s$ be a complex number with real part in the sub-record range
--
--   $$
--   \frac{1}{2} < \operatorname{Re}(s) \le 0.8749570698 .
--   $$
--
--   Assume $\chi$ and $s$ are not simultaneously the trivial character and $s = 1$. Then the analytically continued Dirichlet $L$-function does not vanish:
--
--   $$
--   L(s,\chi) \neq 0 .
--   $$
--
--   This is the target statement [Every Dirichlet character twist is nonzero above the critical line](https://prove2.me/theorems/a2857fa1-ddd4-41af-aa58-12789f53c2a0) restricted to real parts at or below the verified zero-free boundary $0.8749570698 = 4374785349/5000000000$. The complementary range $\operatorname{Re}(s) > 0.8749570698$ is already Proved at [Uniform Dirichlet zero-free boundary 0.8749570698](https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918), so the two statements together cover the entire half-plane $\operatorname{Re}(s) > 1/2$ with no overlap and no gap. The added hypothesis makes this statement strictly weaker than its target, and it isolates exactly the range in which the content of the generalized Riemann hypothesis lives.
--
--   The pole exclusion at $s = 1$ for the principal character is written in the disjunctive form $\chi \neq 1 \vee s \neq 1$, which is logically equivalent to the conjunctive exclusion used by the record theorem; the two are interconverted by De Morgan's laws and require no analytic input.
--
--   **Formalization Note.** The binders and the conclusion are verbatim the target statement, with the single addition of `hcap : s.re ≤ 0.8749570698`, the literal complement of the hypothesis `0.8749570698 < s.re` used by the above-record theorem, so that the two cases partition the half-plane exactly.
-- source:
--   Restriction of the open Prove2Me theorem https://prove2.me/theorems/a2857fa1-ddd4-41af-aa58-12789f53c2a0 (AlpoegeClaudeRH.EveryCharacter) to real parts Re(s) <= 0.8749570698. The complementary range Re(s) > 0.8749570698 is Proved at https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918 (TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound). The unrestricted statement is the nonvanishing half of the generalized Riemann hypothesis for Dirichlet L-functions, in the disjunctive pole-exclusion form; it is logically identical to https://prove2.me/theorems/12cefa1f-e95a-4331-ab94-b8cd47b2d55c (GRH.dirichlet_zero_free_bound) and to its critical-line reformulation https://prove2.me/theorems/6079bb22-0000-0000-0000-000000000000 (GRH.grh_critical_line_iff).

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace AlpoegeClaudeRH

theorem EveryCharacter_below_record
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : 1 / 2 < s.re) (h : χ ≠ 1 ∨ s ≠ 1)
    (hcap : s.re ≤ 0.8749570698) :
    DirichletCharacter.LFunction χ s ≠ 0 := by sorry

end AlpoegeClaudeRH
