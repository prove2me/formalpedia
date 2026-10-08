-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_theorem_3
-- name    : BlackwellDiscreteDP.Stationary.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:01:35.403181+00:00
-- url     : https://prove2.me/theorems/f3eb1f71-1d40-463f-b193-bad5d3c501ed
-- title:
--   Theorem 3 — policy improvement: if every G(s, f) is empty, f^(∞) is β-optimal; an improving g gives g^(∞) > f^(∞)
-- statement:
--   Fix $0\le\beta<1$ and a decision rule $f$. For each state $s$ let $G(s,f)$ be the set of actions $a$ with
--
--   $$i(s,a)+\beta\,p(s,a)\,V_\beta(f^{(\infty)})>V_{\beta,s}(f^{(\infty)}),$$
--
--   where $p(s,a)$ is the row vector $(q(s'\mid s,a))_{s'}$. Then:
--
--   1. if $G(s,f)$ is empty for every $s$, then $f^{(\infty)}$ is $\beta$-optimal (against all policies);
--   2. for every decision rule $g$ such that (a) $g(s)\in G(s,f)$ for some $s$, and (b) $g(s)=f(s)$ whenever $g(s)\notin G(s,f)$, we have $V_\beta(g^{(\infty)})>V_\beta(f^{(\infty)})$, that is, $V_\beta(g^{(\infty)})\ge V_\beta(f^{(\infty)})$ coordinatewise and the two vectors differ.
--
--   This is Howard's policy improvement routine for $\beta<1$: either the current stationary policy is optimal, or switching to improving actions in some states strictly improves it.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, pp. 720–721, Theorem 3

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- Theorem 3, pp. 720–721 (Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593), the policy improvement theorem for a fixed
`β ∈ [0, 1)`. With `G(s, f)` the set of actions `a` such that
`i(s, a) + βp(s, a)V(f^(∞)) > V_s(f^(∞))`:

1. if `G(s, f)` is empty for all `s`, then `f^(∞)` is optimal (§3 sense, against all policies);
2. for any `g` such that (a) `g(s) ∈ G(s, f)` for some `s` and (b) `g(s) = f(s)` whenever
   `g(s) ∉ G(s, f)`, we have `g^(∞) > f^(∞)`, where `>` is "≧ coordinatewise and ≠". -/
theorem theorem_3 {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (f : St → Act) :
    ((∀ s : St, M.G β f s = ∅) → M.IsBetaOptimal β (stationary f)) ∧
    (∀ g : St → Act, (∃ s : St, g s ∈ M.G β f s) →
        (∀ s : St, g s ∉ M.G β f s → g s = f s) →
        M.V β (stationary f) ≤ M.V β (stationary g) ∧
          M.V β (stationary g) ≠ M.V β (stationary f)) := by sorry

end BlackwellDiscreteDP.Stationary
