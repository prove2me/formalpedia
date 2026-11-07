-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_5
-- name    : ApproxDegComp.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:42.789752+00:00
-- url     : https://prove2.me/theorems/d7e2b6ec-6da6-459f-8da8-44be028fa648
-- title:
--   Lemma 5 — error reduction: a multilinear $[0,1]$-valued $\varepsilon$-approximant of degree $K_\varepsilon\,\widetilde{\deg}(F)$
-- statement:
--   For every $\varepsilon\in(0,1/2)$ there is a constant $K_\varepsilon$, depending only on $\varepsilon$, with the following property. Let $F:\{0,1\}^n\to\{0,1\}$ be any Boolean function (any $n$) with $\widetilde{\deg}(F)=d$. Then there is a multilinear real polynomial $q$ of degree at most $K_\varepsilon d$ such that
--
--   $$0\le q(x)\le1\quad\text{and}\quad|q(x)-F(x)|\le\varepsilon\qquad\text{for every }x\in\{0,1\}^n .$$
--
--   Error reduction lets the proof of Theorem 23 start from an approximant of $f\circ g$ with small error $\eta=1/10$ and values in $[0,1]$, at the cost of a constant factor in degree.
--
--   **Formalization Note** $K_\varepsilon$ is quantified after $\varepsilon$ and before the input size and $F$. The cube $\{0,1\}^n$ is indexed by an arbitrary finite type.
--
--   Differences from the source:
--   - encoding: {0,1}ⁿ → ι → Bool for an arbitrary finite type ι; reason: every finite index set is in bijection with [n], so the instances are the same; Theorem 23 applies the lemma on [n]×[m]
--   - reading: "K_ϵ is a constant dependent on ϵ" → K chosen after ε and before the index type and F; reason: the source's K_ε depends on ε only; the proof of Theorem 23 needs K independent of n and F
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 5, p.16

import Mathlib
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_ApproxDegComp_IsMultilinear

namespace ApproxDegComp

/-- **Lemma 5 (Error reduction [12])**, p.16.
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 5, p.16: "Let F : {0, 1}ⁿ → {0, 1} be a Boolean function with d̃eg(F) = d. For
ϵ ∈ (0, 1/2), there exists a multilinear polynomial q with degree at most K_ϵ d that approximates
F such that 0 ≤ q(x) ≤ 1 for every x ∈ {0, 1}ⁿ, |q(x) − F(x)| ≤ ϵ for every x ∈ {0, 1}ⁿ, where
K_ϵ is a constant dependent on ϵ."

**Formalization Note** `K_ε` is chosen after `ε` and before the index type and `F`, so it
depends on `ε` only. The cube `{0,1}ⁿ` is `ι → Bool` for an arbitrary finite type `ι` (the
proof of Theorem 23 applies the lemma on `Fin n × Fin m`). -/
theorem lemma_5 : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ K : ℝ, ∀ (ι : Type) [Fintype ι]
    (F : (ι → Bool) → Bool), ∃ q : MvPolynomial ι ℝ, IsMultilinear q ∧
      (q.totalDegree : ℝ) ≤ K * (approxDeg F : ℝ) ∧
      (∀ x : ι → Bool, 0 ≤ MvPolynomial.eval (cubePt x) q ∧ MvPolynomial.eval (cubePt x) q ≤ 1) ∧
      IsApprox ε F q := by sorry

end ApproxDegComp
