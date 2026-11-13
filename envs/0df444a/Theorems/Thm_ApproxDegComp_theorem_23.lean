-- Prove2me | Theorems.Thm_ApproxDegComp_theorem_23
-- name    : ApproxDegComp.theorem_23
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:33:35.065567+00:00
-- url     : https://prove2.me/theorems/f8385c32-068c-45a1-99ed-f7cf0a99f266
-- title:
--   Theorem 23 — $\widetilde{\deg}(f\circ g)=\Omega(\widetilde{\deg}(f)\,\widetilde{\deg}(g))$ for all total Boolean functions
-- statement:
--   There is an absolute constant $c>0$ such that for all $n,m\ge0$ and all total Boolean functions $f:\{0,1\}^n\to\{0,1\}$ and $g:\{0,1\}^m\to\{0,1\}$,
--
--   $$\widetilde{\deg}(f\circ g)\ \ge\ c\cdot\widetilde{\deg}(f)\,\widetilde{\deg}(g),$$
--
--   where $f\circ g:\{0,1\}^{mn}\to\{0,1\}$ is the block composition $(f\circ g)(x^{(1)},\dots,x^{(n)})=f(g(x^{(1)}),\dots,g(x^{(n)}))$.
--
--   The matching upper bound $\widetilde{\deg}(f\circ g)=O(\widetilde{\deg}(f)\widetilde{\deg}(g))$ is known, so this states that approximate degree composes multiplicatively up to constants for all total functions.
--
--   **Formalization Note** $\Omega(\cdot)$ is a single constant $c>0$ chosen before $n,m,f,g$. Block $i$ of an input $x$ on $[n]\times[m]$ is $j\mapsto x(i,j)$ (`OAI.Paper320.compose`). Constant $f$ or $g$ and $n=0$ or $m=0$ are included.
--
--   Differences from the source:
--   - reading: d̃eg(f∘g) = Ω(d̃eg(f)d̃eg(g)) → ∃ c > 0 such that for all n, m, f, g: c·d̃eg(f)·d̃eg(g) ≤ d̃eg(f∘g); reason: the meaning of Ω with one absolute constant, uniform over n, m, f, g
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 23, p.22 (proof pp.23–24)

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition

namespace ApproxDegComp

/-- **Theorem 23 (Composition Theorem)**, p.22 (proof pp.23–24).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 23, p.22: "Let f : {0, 1}ⁿ → {0, 1} and g : {0, 1}^m → {0, 1} be arbitrary total
Boolean functions. Then d̃eg(f ∘ g) = Ω(d̃eg(f) d̃eg(g))."

**Formalization Note** `Ω(·)` is one absolute constant `c > 0`, chosen before `n, m, f, g`.
`f ∘ g` is the block composition `OAI.Paper320.compose f g` on `Fin n × Fin m`, whose coordinate
`(i, j)` is bit `j` of block `i` (Definition 1 with total `f, g`). Constant `f` or `g` and
`n = 0`, `m = 0` are included. -/
theorem theorem_23 : ∃ c : ℝ, 0 < c ∧ ∀ (n m : ℕ) (f : (Fin n → Bool) → Bool)
    (g : (Fin m → Bool) → Bool),
    c * (approxDeg f : ℝ) * (approxDeg g : ℝ) ≤ (approxDeg (OAI.Paper320.compose f g) : ℝ) := by sorry

end ApproxDegComp
