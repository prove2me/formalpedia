-- Prove2me | Theorems.Thm_DynStrings_theorem_5_1_relative_grammar_size
-- name    : DynStrings.theorem_5_1_relative_grammar_size
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:42.874714+00:00
-- url     : https://prove2.me/theorems/a9639ee5-11bd-46d8-b4fb-52396cea293d
-- title:
--   Theorem 5.1 — tail bound $\Pr[G(X\mid\mathcal C)>T]\le\exp(-c(T/\gamma)\log(T/\Lambda))$ for $T\ge C\Lambda$
-- statement:
--   There are absolute constants $C,c>0$, and an absolute constant $C'$ for the second statement, with the following property. Let $X$ be a non-empty string and $\mathcal C$ a finite collection, both fixed independently of the random orders, and put $\Lambda=\Lambda(X\mid\mathcal C)$ and $\gamma=1+\delta(X\mid\mathcal C)$. Then
--
--   $$\Pr\big[G(X\mid\mathcal C)>T\big]\le\exp\Big(-c\,\frac{T}{\gamma}\,\log\frac{T}{\Lambda}\Big)\qquad\text{for all } T\ge C\Lambda .$$
--
--   Consequently, for every $0<\varepsilon<1$ and $s=\log(1/\varepsilon)$, with probability at least $1-\varepsilon$,
--
--   $$G(X\mid\mathcal C)\le C'\Big(\Lambda+\frac{\gamma s}{\lg(\gamma s/\Lambda)}\Big).$$
--
--   Here $G(X\mid\mathcal C)$ is the number of symbols exclusive to $X$ relative to $\mathcal C$ plus the total arity of the exclusive tuples. The theorem bounds the new grammar a string needs on top of a stored collection; with $\mathcal C=\emptyset$ it gives the static bounds.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: random total orders ≺_k (even k ≥ 2), paused before active, uniformly random on every fixed finite set of active symbols, independent across rounds → any probability space and `ord` with `IsRandomOrders μ ord`: each realization is a choice of the orders, each `ord k` is measurable, every list of distinct well-formed active symbols is increasing with probability 1/n!, and the rounds are independent; reason: the source's assumption written for random variables; every law satisfying the source's assumption extends to the syntactic symbol type with these properties
--   - encoding: with probability at most / at least 1 − ε → the outer measure of the bad event is at most the bound; reason: the bad-event form does not need measurability of the event
--   - encoding: O(·) with absolute constants → an explicit constant quantified before the alphabet, the strings and the orders; reason: the paper's convention (p.13) that hidden constants are absolute
--   - encoding: the grammar: symbols labelling the nodes of T(S), the unfolding of the root → the unfolding of the symbols of the level word S_{κ(|S|)}; reason: by Fact 4.4 this level word is the single root for non-empty S, and it is empty for the empty string
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Theorem 5.1, p.20

import Mathlib
import Definitions.Def_DynStrings_Novelty
open MeasureTheory ProbabilityTheory

namespace DynStrings

/-- **Theorem 5.1** (relative grammar size), p.20.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

There are absolute constants `C, c > 0` (and `C'` for the second statement) with the following
property. Let `X` be a non-empty string and `𝒞` a finite collection, both fixed independently of
the random orders, and put `Λ = Λ(X | 𝒞)` and `γ = 1 + δ(X | 𝒞)`. Then
`Pr[G(X | 𝒞) > T] ≤ exp(−c (T/γ) log(T/Λ))` for all `T ≥ CΛ`. Consequently, for every
`0 < ε < 1` and `s = log(1/ε)`, with probability at least `1 − ε`,
`G(X | 𝒞) ≤ C'(Λ + γ s / lg(γ s / Λ))`.

**Formalization Note.** Probabilities of the bad events are bounded with the outer measure
`μ {ω | …}`; `log` is base 2. -/
theorem theorem_5_1_relative_grammar_size :
    ∃ C c C' : ℝ, 0 < C ∧ 0 < c ∧ 0 < C' ∧
      ∀ (α : Type) [DecidableEq α] (X : List α) (𝒞 : Multiset (List α)) (Ω : Type)
        [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ord : ℕ → Ω → StrSym α → StrSym α → Prop), X ≠ [] → IsRandomOrders μ ord →
        (∀ T : ℝ, C * Lam X 𝒞 ≤ T →
          μ {ω | T < (Grel (fun k => ord k ω) X 𝒞 : ℝ)} ≤
            ENNReal.ofReal
              (Real.exp (-(c * (T / (1 + deltaRel X 𝒞)) * Real.logb 2 (T / Lam X 𝒞))))) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 →
          μ {ω | C' * (Lam X 𝒞 + (1 + deltaRel X 𝒞) * Real.logb 2 (1 / ε) /
              lg ((1 + deltaRel X 𝒞) * Real.logb 2 (1 / ε) / Lam X 𝒞)) <
              (Grel (fun k => ord k ω) X 𝒞 : ℝ)} ≤ ENNReal.ofReal ε) := by sorry

end DynStrings
