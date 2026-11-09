-- Prove2me | Theorems.Thm_AutomaticSelfReduction_Lifting_theorem_5_1
-- name    : AutomaticSelfReduction.Lifting.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:03.906196+00:00
-- url     : https://prove2.me/theorems/12120085-800d-4dfd-95b4-b65f824428be
-- title:
--   Theorem 5.1 — randomized LOCAL lower bound c′·min{log_Δ n, log_{2+b}(ε₀/ε)} for b-dominant 2-separated problems
-- statement:
--   For every constant $c>0$ there is a constant $c'>0$, depending only on $c$, with the following property.
--
--   Let $\Pi=(\Sigma,\Delta,\delta,C_W,C_B)$ be a normalized $b$-dominant 2-separated problem with $\Delta\ge\delta$, let $(S,\mu)$ be any shared-randomness probability space, and let $\mathcal G$ be a family of $(\Delta,\delta)$-biregular 2-coloured graphs on $n$ vertices, each of girth at least $c\log_\Delta n$. Let $\varepsilon_0>0$ be a lower bound on the expected error of any $0$-round algorithm for $\Pi$ that has $0$ white error: every such algorithm has expected error at least $\varepsilon_0$ on some graph of $\mathcal G$. Then every $T$-round algorithm for $\Pi$ on $\mathcal G$ in the randomized LOCAL model with $0$ white error and expected error at most $\varepsilon\ge0$ on every graph of $\mathcal G$ satisfies
--   $$
--   T\;\ge\;c'\,\min\Bigl\{\log_\Delta n,\ \log_{2+b}\frac{\varepsilon_0}{\varepsilon}\Bigr\},
--   $$
--   where for $\varepsilon=0$ the right-hand side is $c'\log_\Delta n$.
--
--   Here the error of an output is the sum over all nodes of the number of incident labels that must be changed to make the node's configuration valid, and algorithms may be non-computable, use unboundedly many random bits and shared randomness. The theorem converts a lower bound on the error of $0$-round algorithms into a round lower bound that grows with $\log(\varepsilon_0/\varepsilon)$, with a logarithm base depending only on the dominance parameter $b$ and not on the degree.
--
--   **Formalization Note** The constant $c'$ is chosen before the problem, $b$, the degrees, $n$, the family, the randomness space, $\varepsilon_0$, $\varepsilon$ and the algorithm. Expected errors are lower Lebesgue integrals in $[0,\infty]$, compared with $\varepsilon$ through `ENNReal.ofReal`. Zero-round rules in the premise have zero white error on every execution; the algorithm in the conclusion is only required to have expected white error $0$ on each graph.
--
--   Differences from the source:
--   - reading: a family G of graphs of girth ≥ c log_Δ n; ε₀ a lower bound on the expected error of any 0-round algorithm with 0 white error → for each n a family 𝒢 of n-vertex graphs; every 0-round algorithm with zero white error on every execution has expected error ≥ ε₀ on some graph of 𝒢, and the T-round algorithm meets its guarantee on every graph of 𝒢; reason: algorithms know n; this is the worst-case-over-the-family reading; a bound on every graph implies the premise, and restricting the premise to everywhere-valid rules only weakens it
--   - reading: 0 white error of the T-round algorithm → expected white error 0 on each graph of 𝒢; reason: the weakest reading of the hypothesis (equivalently, almost surely zero)
--   - reading: log_{2+b}(ε₀/ε) at ε = 0 (undefined) → bound c′ log_Δ n; reason: this is the limit of the printed expression as ε → 0; Lean's ε₀/0 = 0 would weaken the bound
--   - encoding: ε₀ a lower bound, in log_{2+b}(ε₀/ε) → hypothesis 0 < ε₀; reason: for ε₀ ≤ 0 the printed logarithm is undefined and the only possible content is T ≥ 0
--   - encoding: expected error at most ε → 0 ≤ ε and the [0,∞]-valued expected error is at most ENNReal.ofReal ε; reason: the source's ε bounds a nonnegative expected error; in Lean ENNReal.ofReal ε = 0 for ε < 0, so a negative ε would act as ε = 0 while ε₀/ε turned negative and Real.logb took its absolute value; 0 ≤ ε excludes only this meaningless case
--   - reading: ports "assigned by the nodes using their own random bits", replacing w.l.o.g. an adversarial assignment (§4) → each node's port order is uniformly random, independent of its random bits and of all other nodes' randomness; reason: the source does not fix the law of the assignment; a uniform independent order is the reading under which the w.l.o.g. remark holds and the conditional law of a neighbour's output in §5.1 does not depend on port numbers the black node cannot see
--   - encoding: randomized LOCAL model with unbounded messages, private random bit strings and shared randomness → full-information states, infinite product of fair coins per node, arbitrary probability space (S, μ), the same (S, μ) for the 0-round rules and the algorithm, measurable rules; reason: messages are unbounded, so every protocol's output is a function of the full-information state; a one-point S is private randomness only
-- source:
--   Alkida Balliu, Francesco d’Amore, Dennis Olivetti, Distributed Lower Bounds via Automatic Self-Reduction, STOC 2027 submission #338 (October 2026), Theorem 5.1, printed p. 12 (PDF p. 13); informal version Theorem 2.10, printed p. 8 (PDF p. 9); proof printed p. 13 (PDF p. 14)

import Definitions.Def_AutomaticSelfReduction_Lifting_Local

open MeasureTheory

namespace AutomaticSelfReduction.Lifting

/-- Theorem 5.1 (Balliu–d'Amore–Olivetti, STOC 2027 submission #338, PDF p. 13, printed p. 12).
For every `c > 0` there is `c' > 0` such that: for every normalized 2-separated `b`-dominant
problem `Π = (Σ, Δ, δ, C_W, C_B)` with `Δ ≥ δ`, every shared-randomness space `(S, μ)`, every
`n` and every family `𝒢` of `(Δ, δ)`-biregular 2-coloured `n`-vertex graphs of girth at least
`c log_Δ n`, if every `0`-round algorithm with `0` white error has expected error at least
`ε₀ > 0` on some graph of `𝒢`, then every `T`-round algorithm with `0` white error and expected
error at most `ε` on every graph of `𝒢` has `T ≥ c' · min{log_Δ n, log_{2+b}(ε₀/ε)}`
(for `ε = 0`, `T ≥ c' log_Δ n`). -/
theorem theorem_5_1 :
    ∀ c : ℝ, 0 < c → ∃ c' : ℝ, 0 < c' ∧
      ∀ (L : Type) [Fintype L] [DecidableEq L] (Δ δ : ℕ) (P : Problem L Δ δ) (b : ℕ),
        P.IsNormalized → P.TwoSeparated → P.Dominant b → δ ≤ Δ →
        ∀ (S : Type) [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
          (n : ℕ) (𝒢 : Set (Instance n Δ δ)),
          (∀ G ∈ 𝒢, G.GirthAtLeast (c * Real.logb Δ n)) →
          ∀ ε₀ : ℝ, 0 < ε₀ →
            (∀ A₀ : Algorithm S L Δ δ 0, A₀.WhiteValid P →
              ∃ G ∈ 𝒢, ENNReal.ofReal ε₀ ≤ expError P μ A₀ G) →
            ∀ (T : ℕ) (ε : ℝ), 0 ≤ ε → ∀ A : Algorithm S L Δ δ T,
              (∀ G ∈ 𝒢, expWhiteError P μ A G = 0 ∧ expError P μ A G ≤ ENNReal.ofReal ε) →
              c' * (if ε = 0 then Real.logb Δ n
                else min (Real.logb Δ n) (Real.logb (2 + b) (ε₀ / ε))) ≤ T := by sorry

end AutomaticSelfReduction.Lifting
