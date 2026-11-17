-- Prove2me | Theorems.Thm_ApproxDegComp_Supplement_theorem_31
-- name    : ApproxDegComp.Supplement.theorem_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:01:57.475887+00:00
-- url     : https://prove2.me/theorems/0adf9f24-4a1c-4385-87e0-0b276c76f95f
-- title:
--   Theorem 31 — $\mathrm{R}(f)\le C\log(n+1)\,\mathrm{noisyR}(f)$ for every non-constant partial $f$
-- statement:
--   **Noisy queries save at most a logarithm.** There is an absolute constant $C>0$ such that for every $n\ge0$ and every non-constant partial Boolean function $f:D\subseteq\{0,1\}^n\to\{0,1\}$ (i.e. $f(x)\neq f(y)$ for some $x,y\in D$),
--
--   $$\mathrm{R}(f)\ \le\ C\,\log(n+1)\,\mathrm{noisyR}(f).$$
--
--   Here $\mathrm{R}(f)$ is the bounded-error randomized query complexity: the least $d$ such that some probability distribution over deterministic decision trees, each making at most $d$ queries, errs with probability at most $1/3$ on every $x\in D$. $\mathrm{noisyR}(f)$ is the noisy randomized query complexity: the infimum, over finite-support distributions of finite noisy decision trees that err with probability at most $1/3$ on every $x\in D$, of the worst-case expected cost $\max_{x\in D}\mathbb E[\sum_t\gamma_t^2]$. $\log$ is the natural logarithm.
--
--   The paper calls this its main result. Combined with the known bound $\mathrm{R}(f\circ g)=\Omega(\mathrm{noisyR}(f)\,\mathrm{R}(g))$ it gives $\mathrm{R}(f\circ g)=\Omega(\mathrm{R}(f)\mathrm{R}(g)/\log(n+1))$ for all partial $f,g$ (Corollary 2).
--
--   **Formalization Note** $\mathrm{R}$ is the published `NoPerfectRandComp.R`. Its depth bound is counted on every input of the cube, which is equivalent because trees can be truncated off the domain.
--
--   Differences from the source:
--
--   - encoding: the constant C → one constant C > 0 quantified before n and f; reason: the source's C is absolute (its proof derives it from absolute constants); requiring C > 0 changes nothing since the right side is nondecreasing in C
--   - encoding: a partial function f : D ⊆ {0,1}ⁿ → {0,1} and "non-constant" → NoPerfectRandComp.PartialFn (Fin n) with ∃ x ∈ dom, ∃ y ∈ dom, val x ≠ val y; reason: Lean representation, same objects
--   - encoding: finite-support distributions over finite noisy decision trees, cost(A, x), max over D → a PMF with finite support over an inductive tree type, costs as finite sums, ⨆ over the subtype D; reason: Lean representation of Definitions 6–8, same quantities
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Theorem 31, p.33 (Definitions 5–8, p.12)

import Mathlib
import Definitions.Def_NoPerfectRandComp_Reps
import Definitions.Def_ApproxDegComp_Supplement_noisyR

namespace ApproxDegComp

namespace Supplement

/-- **Theorem 31**, p.33 (the paper's main result on randomized query complexity).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Theorem 31, p.33: "For a non-constant partial Boolean function
f : D ⊆ {0,1}ⁿ → {0,1}, R(f) ≤ C log (n + 1) noisyR(f)."

**Formalization Note** `C` is one absolute constant, chosen before `n` and `f` (the proof on
pp.33–34 derives it from the absolute constants of Lemmas 10, 12 and 29). `f` is any partial
Boolean function (`NoPerfectRandComp.PartialFn (Fin n)`, arbitrary domain `D`), non-constant on
`D`. `R(f)` is the published `NoPerfectRandComp.R` (Definition 5: least worst-case number of
queries of a distribution over deterministic decision trees with error `≤ 1/3` on `D`).
`noisyR(f)` is Definition 8 over finite-support distributions of finite noisy decision trees
(Definitions 6–7), worst-case expected cost over `D`, error `≤ 1/3` on `D`. `log` is `Real.log`. -/
theorem theorem_31 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : NoPerfectRandComp.PartialFn (Fin n)),
    (∃ x ∈ f.dom, ∃ y ∈ f.dom, f.val x ≠ f.val y) →
    (NoPerfectRandComp.R f : ℝ) ≤ C * Real.log ((n : ℝ) + 1) * noisyR f := by sorry

end Supplement

end ApproxDegComp
