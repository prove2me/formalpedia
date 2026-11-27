-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_theorem_3_6
-- name    : AccelNewtonDinkelbach.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:02:06.72571+00:00
-- url     : https://prove2.me/theorems/09f329bb-dcd0-507e-8b6c-b14880db23f4
-- title:
--   Theorem 3.6 — Algorithm 1 converges in $O(m\log m)$ iterations for linear fractional combinatorial optimization
-- statement:
--   There are constants $C>0$ and $m_0$ with the following property. Let $m\ge m_0$, let $D\subseteq\{0,1\}^m$ be nonempty, and let $c,d\in\mathbb R^m$ satisfy $d^\top x>0$ for every $x\in D$ (linear fractional combinatorial optimization, §3.1). Let $f(\delta)=\min_{x\in D}(c-\delta d)^\top x$. Then every run $\delta^{(1)},\dots,\delta^{(N)}$ of Algorithm 1 (Look-aheadNewton) on $f$, from any admissible start ($f(\delta^{(1)})\le 0$, $g^{(1)}\in\partial f(\delta^{(1)})$, $g^{(1)}<0$) and with any supergradient answers of the oracle, has
--
--   $$N\le C\,m\log m$$
--
--   iterates. In particular Algorithm 1 terminates within that many iterations.
--
--   **Formalization Note** $f$ is finite, so its effective domain is $\mathbb R$; $f(\delta)$ is given as the least element of $\{(c-\delta d)^\top x : x\in D\}$. Runs are the published base definitions `IsRun` with `LookAheadStep`. The logarithm is natural; the paper's $\log_2$ changes only $C$.
--
--   Differences from the source:
--   - reading: converges in O(m log m) iterations → ∃ C > 0 and ∃ m₀, chosen before every instance, with N ≤ C·m·log m for every m ≥ m₀ and every prefix δ(1..N) of a run; reason: the definition of O(·) in the parameter m; a bound on every prefix of a run is termination within the bound
--   - generalization: oracle answers from a linear optimization oracle over D (supergradients −d⊤x for x ∈ arg min) → arbitrary supergradients in ∂f at every call; reason: the linear-optimization answers are supergradients, so every run of the paper is a run here; the proof uses only Lemmas 3.3 and 3.4, which hold for arbitrary oracle answers
--   - encoding: log = log₂ (p.6) → Real.log; reason: the two differ by the factor ln 2, absorbed in C
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 3.6 and §3.1, p.9

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_IsRun
import Definitions.Def_AccelNewtonDinkelbach_LookAheadStep

namespace AccelNewtonDinkelbach.Supplement

open scoped BigOperators

set_option autoImplicit false

/-- **Theorem 3.6 (Algorithm 1 takes `O(m log m)` iterations on linear fractional combinatorial
optimization).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Theorem 3.6, p.9: "Algorithm 1 converges in
O(m log m) iterations for linear fractional combinatorial optimization problems."

The setting is §3.1, p.9 (problem (1) of p.1 with `D ⊆ {0,1}^m`): a nonempty `D ⊆ {0,1}^m` and
`c, d ∈ ℝ^m` with `d⊤x > 0` for every `x ∈ D`, and the parametric function
`f(δ) = min_{x∈D} (c − δd)⊤x` of (2). There are absolute constants `C > 0` and `m₀` such that for
every `m ≥ m₀`, every such instance and every run `δ(1), …, δ(N)` of Algorithm 1 on `f`, the number
of iterates satisfies `N ≤ C · m log m`.

**Formalization Note**
1. `O(m log m)` is read with its definition: `∃ C > 0, ∃ m₀`, both chosen before every
   instance, with the bound for all `m ≥ m₀`. The logarithm is `Real.log`; the paper's `log₂`
   (p.6) changes only `C`.
2. `f δ` is given as the least element of `{(c − δd)⊤x : x ∈ D}` (the paper's `min`; `D` is
   finite and nonempty, so it exists). `f` is finite, so its effective domain is all of `ℝ`
   (`dom = Set.univ`) and it is concave.
3. Runs are the published base definitions: `IsRun (LookAheadStep univ f) univ f δ g N` is a
   (prefix of an) execution of Algorithm 1 from any admissible start `δ(1)`, `g(1) ∈ ∂f(δ(1))`,
   `f(δ(1)) ≤ 0`, `g(1) < 0`, with arbitrary supergradient answers at every oracle call. The
   paper's oracle answers come from a linear optimization oracle over `D`; those answers are
   supergradients, so the Lean covers them. Bounding the length of every prefix asserts
   termination within the bound. Iterates are 1-indexed. -/
theorem theorem_3_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ D : Set (Fin m → ℝ), D.Nonempty → (∀ x ∈ D, ∀ i, x i = 0 ∨ x i = 1) →
      ∀ c d : Fin m → ℝ, (∀ x ∈ D, 0 < ∑ i, d i * x i) →
      ∀ f : ℝ → ℝ, (∀ δ : ℝ, IsLeast ((fun x => ∑ i, (c i - δ * d i) * x i) '' D) (f δ)) →
      ∀ (δ g : ℕ → ℝ) (N : ℕ),
        AccelNewtonDinkelbach.IsRun (AccelNewtonDinkelbach.LookAheadStep Set.univ f) Set.univ f
          δ g N →
        (N : ℝ) ≤ C * ((m : ℝ) * Real.log m) := by sorry

end AccelNewtonDinkelbach.Supplement
