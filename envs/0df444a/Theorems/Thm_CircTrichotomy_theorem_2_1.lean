-- Prove2me | Theorems.Thm_CircTrichotomy_theorem_2_1
-- name    : CircTrichotomy.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:33.480416+00:00
-- url     : https://prove2.me/theorems/72c84aab-df35-46e0-91a6-53dc08f43b02
-- title:
--   Theorem 2.1 — circuit complexity trichotomy for regular languages
-- statement:
--   **Theorem 2.1** (Circuit Complexity Trichotomy for Regular Languages). Let $\Sigma$ be a finite non-empty alphabet and $L\subseteq\Sigma^+$ a regular language, and let $c(L)(n)$ be the least number of $\wedge/\vee$ gates of an $n$-circuit (unbounded fan-in, subset-encoded inputs, input gates free) accepting exactly the words of length $n$ in $L$. Then **precisely one** of the following holds:
--   1. **Constant:** $c(L)\in O(1)$.
--   2. **Almost logarithmic:** $c(L)\in\Omega(\log n)\cap O(\log n\log\log n)$.
--   3. **Linear:** $c(L)\in\Omega(n)\cap O(n)$.
--
--   Here $\Omega$ is the Hardy–Littlewood $\Omega$: $f\in\Omega(g)$ iff $f(n)\ge c\,g(n)$ for some $c>0$ and infinitely many $n$.
--
--   The theorem leaves no regular language with circuit complexity strictly between $\log n\log\log n$ and $n$, or between $1$ and $\log n$.
--
--   Differences from the source:
--   - encoding: a regular language L ⊆ Σ⁺ over a finite non-empty alphabet Σ → Language.IsRegular L (Mathlib: accepted by a finite automaton), [] ∉ L, Fintype α, Nonempty α; reason: p.17 identifies regular, recognizable by a finite semigroup, and accepted by a finite automaton; L ⊆ Σ⁺ is [] ∉ L
--   - encoding: n-circuits (G, ≺, λ, out) of Definition A.2 → Circuit α n m: non-input gates numbered in topological order, each with a non-empty list of wire sources (input labels (i, Γ) and earlier gates); outputs are the gates read by no gate, in bijection with Fin m; reason: every finite DAG has a topological numbering; one input gate per label (duplicate input gates change no value, size or depth); size and depth as in Definition A.2
--   - encoding: functions ℕ>0 → ℝ≥0 (c(L), sizes, depths) → functions ℕ → ℝ; c(L)(0) = 0 and family size/depth 0 at n = 0; reason: O, o and Hardy–Littlewood Ω only look at all but finitely many, resp. infinitely many n, so the value at n = 0 is never seen
--   - encoding: log → Real.logb 2; reason: log is base two (p.58); every asymptotic class used is invariant under the base
--   - encoding: precisely one of (1), (2), (3) → (A ∧ ¬B ∧ ¬C) ∨ (¬A ∧ B ∧ ¬C) ∨ (¬A ∧ ¬B ∧ C); reason: literal exclusive disjunction of three statements
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.1, p.3

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_HLOmega

set_option autoImplicit false

namespace CircTrichotomy

/-- **Theorem 2.1 (Circuit Complexity Trichotomy for Regular Languages)** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.1, p.3):
"Let L ⊆ Σ⁺ be a regular language. Then precisely one of the following holds, where Ω refers to
Hardy-Littlewood notation (see Definition A.1 for more details):
(1) Constant: c(L) ∈ O(1).
(2) Almost Logarithmic: c(L) ∈ Ω(log n) ∩ O(log n log log n).
(3) Linear: c(L) ∈ Ω(n) ∩ O(n)."

For every finite non-empty alphabet `α` and every regular `L ⊆ α⁺`, exactly one of the three
clauses holds for `c = c(L)` (`circuitComplexity L`, as a real function).

**Formalization Note**
* "Precisely one" is `(A ∧ ¬B ∧ ¬C) ∨ (¬A ∧ B ∧ ¬C) ∨ (¬A ∧ ¬B ∧ C)`.
* `O` is `BigO` (p.17), `Ω` is the Hardy–Littlewood `HLOmega` (Definition A.1: infinitely many `n`).
* `log` is `Real.logb 2`; every class is invariant under the base of the logarithm.
* `O(1)` is `O` of the constant function `1`.
* Regularity is Mathlib's `Language.IsRegular` (accepted by a finite automaton), which the paper
  identifies with recognizability by a finite semigroup (p.17). `L ⊆ Σ⁺` is `[] ∉ L`. -/
theorem theorem_2_1 {α : Type} [Fintype α] [Nonempty α] (L : Language α) (hreg : L.IsRegular)
    (hL : [] ∉ L) :
    let c : ℕ → ℝ := fun n => (circuitComplexity L n : ℝ)
    let A : Prop := BigO c (fun _ => 1)
    let B : Prop := HLOmega c (fun n => Real.logb 2 n) ∧
      BigO c (fun n => Real.logb 2 n * Real.logb 2 (Real.logb 2 n))
    let C : Prop := HLOmega c (fun n => (n : ℝ)) ∧ BigO c (fun n => (n : ℝ))
    (A ∧ ¬ B ∧ ¬ C) ∨ (¬ A ∧ B ∧ ¬ C) ∨ (¬ A ∧ ¬ B ∧ C) := by sorry

end CircTrichotomy
