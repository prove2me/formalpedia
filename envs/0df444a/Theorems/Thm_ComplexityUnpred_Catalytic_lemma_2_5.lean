-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_lemma_2_5
-- name    : ComplexityUnpred.Catalytic.lemma_2_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:02:31.829272+00:00
-- url     : https://prove2.me/theorems/2081b3b2-2b73-4d05-92b8-b90fff1b926f
-- title:
--   Lemma 2.5 — averaging: small advantage on S gives a string of S on which few predictors succeed
-- statement:
--   Let $n\in\mathbb N$ and $\epsilon>0$. Let $\mathcal P=\{P_1,\dots,P_m\}$ ($m\ge1$) be a family of (middle-bit or next-bit) predictors over $\{0,1\}^n$, and let $S\subseteq\{0,1\}^n$ be a non-empty multiset with $\mathrm{adv}_{U(S)}(\mathcal P)<\epsilon$, where $\mathrm{adv}_{U(S)}(\mathcal P)=\max_j\max\{0,\Pr_{s\sim U(S)}[P_j\text{ succeeds on }s]-\tfrac12\}$. Then some $s\in S$ satisfies
--   $$\Pr_{P\in\mathcal P}[P\text{ succeeds on }s]<\frac12+\epsilon,$$
--   the probability being over a uniformly random member of the indexed family.
--
--   This averaging step is used throughout the paper; in §4 it turns a solution of UNPRED into a single string on which the predictors of a graph do badly (Corollary 4.7).
--
--   **Formalization Note** A predictor enters only through the set of strings it succeeds on, so the family is given as a non-empty finite indexed family of success tests $T_i:\{0,1\}^n\to\{0,1\}$; `testAdvFam S T` is $\mathrm{adv}_{U(S)}(\mathcal P)$ and `famProb T s` is $\Pr_{P\in\mathcal P}[P\text{ succeeds on }s]$.
--
--   Differences from the source:
--   - generalization: a family of middle-bit or next-bit predictors → any non-empty finite family of success tests T i : {0,1}ⁿ → Bool; reason: each middle-bit or next-bit predictor is the test 'P succeeds on s', so both of the paper's cases are instances
--   - generalization: n ∈ ℕ = {1, 2, …} → n : ℕ, n = 0 allowed; reason: covers every n ≥ 1
--   - encoding: multiset S, U(S), and Pr over the family P = {P₁, …, P_m} → Multiset (Fin n → Bool) with counting averages; the family indexed by a Fintype ι, members counted with multiplicity; values in ℝ; reason: Lean convention; same instances
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 20, Lemma 2.5

import Mathlib
import Definitions.Def_ComplexityUnpred_Catalytic_Predictor

namespace ComplexityUnpred.Catalytic

/-- **Lemma 2.5** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 20), averaging. For a non-empty
finite family of predictors over `{0,1}ⁿ`, each given by its success test `T i` (the strings it
succeeds on; middle-bit and next-bit predictors alike), and a non-empty multiset `S ⊆ {0,1}ⁿ`
with `adv_{U(S)}(𝒫) < ϵ`, some `s ∈ S` has `Pr_{P∈𝒫}[P succeeds on s] < 1/2 + ϵ`. -/
theorem lemma_2_5 {n : ℕ} {ι : Type} [Fintype ι] [Nonempty ι]
    (T : ι → (Fin n → Bool) → Bool) (ε : ℝ) (hε : 0 < ε)
    (S : Multiset (Fin n → Bool)) (hS : S ≠ 0) (hadv : testAdvFam S T < ε) :
    ∃ s ∈ S, famProb T s < 1 / 2 + ε := by sorry

end ComplexityUnpred.Catalytic
