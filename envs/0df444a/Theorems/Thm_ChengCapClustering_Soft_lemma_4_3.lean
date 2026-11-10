-- Prove2me | Theorems.Thm_ChengCapClustering_Soft_lemma_4_3
-- name    : ChengCapClustering.Soft.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:53:19.635204+00:00
-- url     : https://prove2.me/theorems/79b6b012-3b44-49a3-9c48-916755e85faa
-- title:
--   Lemma 4.3 — a polynomially computable family of $O(|X|^7)$ hierarchical decompositions with $\Pr[(x,y)\ \Lambda\text{-bad}]\le2^{11}D/\Lambda$
-- statement:
--   Let $X$ be a finite set with at least two points, minimum distance $2$ between distinct points and doubling dimension at most $D$ (§4.2). There is a family $\mathcal D$ of $O(|X|^7)$ hierarchical decompositions of $X$, computable in time polynomial in $|X|$ and $H$, and a probability distribution on $\mathcal D$ such that for all $\Lambda\ge1$ and all distinct $x,y\in X$, $\Pr_{D\sim\mathcal D}[(x,y)\text{ is }\Lambda\text{-bad in }D]\le 2^{11}D/\Lambda$.
--
--   Differences from the source:
--   - encoding: an algorithm in the arithmetic model ("arithmetic operations and evaluations of dist(x, y)^z count as single steps") → an admissible program of `ChengCapClustering.Soft.Machine` (rational literals; parameters passed as real input) run on the stated input layout, halting within the stated number of steps with the stated output layout; reason: the source's cost model made operational; the output layout only names where the computed object is written
--   - reading: computable in time polynomial in |X| and H; a family of O(|X|^7) members → one program and one constant C for every D and every X: at most C (N + H + 2)^C steps and at most C N^7 members; reason: the construction of §4.2 does not depend on D; the strongest reading of the polynomial bound
--   - encoding: a family with a probability distribution; Pr[(x,y) is Λ-bad] → r decompositions with weights w ≥ 0 summing to 1, written to the output; the total weight of the members in which the pair is Λ-bad; reason: a finite distribution on a listed family
-- source:
--   Cheng, Mo, Ding 2026, Constant-Factor Approximation for Capacitated Clustering in Low Dimension with (1+ε)k Centers, arXiv:2610.40625 (held manuscript SHA-256 9d298191e7086ee0bbea53e5a3e4e9b0fe88c438ed58257f01f3c524a8ac4edb; arXiv version suffix unresolved, citation hold), Lemma 4.3, printed p. 14 / PDF p. 16

import Mathlib
import Definitions.Def_MinSumDimRed_Doubling_Metric
import Definitions.Def_ChengCapClustering_Soft_Machine
import Definitions.Def_ChengCapClustering_Soft_Clustering
import Definitions.Def_ChengCapClustering_Soft_Network

open MinSumDimRed.Doubling Classical

universe u

namespace ChengCapClustering.Soft

/-- Lemma 4.3 (Decomposition family), printed p. 14 / PDF p. 16. For a finite set `X` (an injective
list `x`) with at least two points, minimum distance `2` and doubling dimension at most `D`, one
program computes, in time polynomial in `|X|` and `H`, a family of `O(|X|^7)` hierarchical
decompositions of `X` and a probability distribution on it under which every pair of distinct
points is `Λ`-bad with probability at most `2^{11} D / Λ`, for every `Λ ≥ 1`. The program and the
constant `C` are the same for every `D` and every `X`. -/
theorem lemma_4_3 :
    ∃ prog : Program, Admissible prog ∧ ∃ C : ℕ,
      ∀ (V : Type u) [MetricSpace V] (D : ℝ) (N : ℕ) (x : Fin N → V),
        Function.Injective x → MinDistTwo x → IsDoublingWith (Set.range x) D →
        HaltsWithin prog [(N : ℤ)] (distanceList x)
          ((C : ℝ) * ((N + topLevel x + 2 : ℕ) : ℝ) ^ C)
          (fun s => ∃ (r : ℕ) (fam : Fin r → HierDecomp N) (w : Fin r → ℝ),
            (r : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ 7 ∧
            (∀ d, (fam d).IsValid x) ∧ (∀ d, 0 ≤ w d) ∧ ∑ d, w d = 1 ∧
            (∀ Λ : ℝ, 1 ≤ Λ → ∀ i j, i ≠ j →
              ∑ d ∈ Finset.univ.filter (fun d => (fam d).IsBad x Λ i j), w d ≤
                (2 : ℝ) ^ 11 * D / Λ) ∧
            OutputIs s ((r : ℤ) :: (List.ofFn fun d => (fam d).encode).flatten) (List.ofFn w)) := by sorry

end ChengCapClustering.Soft
