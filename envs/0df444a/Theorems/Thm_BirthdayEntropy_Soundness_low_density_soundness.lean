-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_low_density_soundness
-- name    : BirthdayEntropy.Soundness.low_density_soundness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:43.44433+00:00
-- url     : https://prove2.me/theorems/c7fc9ec6-f415-44fa-b22c-752ce5c97081
-- title:
--   Theorem 2.1 — Entropy-weighted low-density soundness
-- statement:
--   For every fixed real $d\ge1$ and $\varepsilon>0$ there exist $C_0,c>0$ and $0<x_0<1/2$, depending only on $d,\varepsilon$, such that the following two implications hold.
--
--   1. For every Boolean ternary CSP $\varphi$ on $n$ nonisolated variables with $m$ indexed constraints, arbitrary predicates on three distinct variables, at most $d$ occurrences of each variable, and at least $\varepsilon m$ violated constraints under every global assignment, every integer $\ell$ with $2\le\ell\le x_0n$ and $\ell\log(en/\ell)\ge C_0\log(n+1)$ satisfies
--   $$\rho^*\!\left(\binom n\ell\right)\le2\exp\!\left(-c\frac{\ell^3}{n^2\log(en/\ell)}\right).$$
--   The maximum is computed over all $K$-element sets of distinct vertices, with missing views, repeated views and all local labels retained.
--
--   2. For every satisfiable indexed Boolean ternary CSP, independently of the NO promise, and every $1\le\ell\le n$,
--   $$G_{\varphi,\ell}\text{ contains a clique of size }K=\binom n\ell.$$
--
--   The constants are chosen before every instance and scale. This is the full entropy-weighted density goal, together with a separate perfect-completeness implication. It makes no complexity-theoretic hardness assertion.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: log(en/ell) and the maximum density → log(exp(1)/(ell/n)) and the maximum of the explicit nonempty finite selection family; reason: the logarithms agree on admitted scales and the finite maximum is attained; no default supremum is used
--   - generalization: the completeness clause accompanying the soundness scale and bounded-occurrence source class → completeness for every indexed ternary CSP and every 1<=ell<=n; reason: Lemma B.1 proves this full graph-domain implication, which specializes to the printed clause
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Theorem 2.1, PDF pp3,4 / printed pp2,3

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Theorem 2.1, PDF pp3–4 / printed pp2–3. Constants precede all
instances and all scales. The independent YES implication is not under Gap.
The completeness domain is extended to the full 1≤ell≤n domain of Lemma B.1. -/
theorem low_density_soundness (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ c x₀ : ℝ, 0 < C₀ ∧ 0 < c ∧ 0 < x₀ ∧ x₀ < 1/2 ∧
      (∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
        ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
          maxDensity φ ℓ ≤ 2 * Real.exp
            (-c * (ℓ : ℝ)^3 / ((n : ℝ)^2 * logScale n ℓ))) ∧
      (∀ (n m : ℕ) (φ : CSP n m) (ℓ : ℕ),
        1 ≤ ℓ → ℓ ≤ n → Satisfiable φ → HasTargetClique φ ℓ) := by sorry

end BirthdayEntropy.Soundness
