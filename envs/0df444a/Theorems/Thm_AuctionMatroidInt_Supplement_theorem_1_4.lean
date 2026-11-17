-- Prove2me | Theorems.Thm_AuctionMatroidInt_Supplement_theorem_1_4
-- name    : AuctionMatroidInt.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:24:00.758018+00:00
-- url     : https://prove2.me/theorems/29246286-6fd0-4405-a64c-875f3cdf505c
-- title:
--   Theorem 1.4 — semi-streaming $(1-\varepsilon)$-approximation for matroid intersection with $O(1/\varepsilon^2)$ passes, $O(r)$ space and $O(n\log r/\varepsilon^2)$ independence queries
-- statement:
--   There are absolute constants $C$ and $c$ and, for every $n$ and $\varepsilon$, a legal deterministic semi-streaming algorithm $A_{n,\varepsilon}$ on the ground set $[n]$ with the following properties for every $0<\varepsilon<1$, all matroids $M_1=([n],\mathcal I_1)$ and $M_2=([n],\mathcal I_2)$ (loops allowed) and every order of the stream (each element exactly once, the same order in every pass). Let $r$ be the maximum size of a common independent set. Then
--
--   1. the run halts with an output $X\in\mathcal I_1\cap\mathcal I_2$ with $|X|\ge(1-\varepsilon)\,r$;
--   2. it starts at most $C/\varepsilon^{2}$ passes;
--   3. it makes at most
--   $$
--   C\,\frac{n\log(r+2)}{\varepsilon^{2}}
--   $$
--   independence queries, each on a subset of the stored elements and the arriving element;
--   4. at every moment its memory holds at most $C\,(r+1)$ words;
--   5. every number it ever stores is below $(n+2)^{c}$, i.e. fits in $O(\log n)$ bits.
--
--   This is the first semi-streaming $(1-\varepsilon)$-approximation for matroid intersection with $(1/\varepsilon)^{O(1)}$ passes; it is deterministic and its space is linear in $r$.
--
--   **Formalization Note** The model is `StreamAlg` with `StreamAlg.IsLegal`; oracle answers come from the published `AuctionMatroidInt.indepOracle`. The constants are chosen before $n$, $\varepsilon$, the matroids and the stream order; the algorithm depends on $(n,\varepsilon)$ only. No assumption of §2.1 is made.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset (Fin n) → Prop (ground set = Fin n); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: a deterministic semi-streaming algorithm: elements of E arrive one by one as a stream, several sequential passes, independence oracles for M1, M2 queried only on subsets of the elements stored in memory (and the arriving element, §6.2), space counted in machine words → ∃ A : (n : ℕ) → ℝ → StreamAlg n with StreamAlg.IsLegal (renaming-equivariant, queries ⊆ stored elements ∪ arriving element), run by StreamAlg.config; passes = passes started, queries = query steps, space = memory length at every micro-step; reason: the paper names no instruction set; this is §2.1's query-complexity convention (free computation, counted oracle calls) with §6.1's access and space restrictions; renaming-equivariance expresses that elements are objects delivered by the stream rather than names the algorithm can compute
--   - encoding: each machine word has O(log n) bits (footnote 3) → ∃ c (absolute) with every stored number < (n + 2)^c; an element cell is one word; reason: a word of O(log n) bits holds exactly the numbers below a fixed power of n (n + 2 to cover n ≤ 1)
--   - reading: the stream (order unspecified) → every order σ of Fin n (each element exactly once), the same order in every pass; reason: §6.2 processes elements "in the order in which they arrive" and requires correctness for an arbitrary order; a multi-pass stream re-reads the same input
--   - reading: O(1/ε²) passes, O(r) space, O(n log(r)/ε²) queries → ∃ C (absolute): passes ≤ C/ε², memory ≤ C·(r + 1) words, queries ≤ C·n·log(r + 2)/ε² (natural log); reason: the printed rates vanish at r ≤ 1 (r = 0 is possible with loops) while any algorithm stores or queries something; the readings agree with the printed ones up to a constant for r ≥ 2
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Theorem 1.4 and footnote 3, p.5 (PDF p.7); restated p.32 (PDF p.34), proof §6.2

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_QueryTree
import Definitions.Def_AuctionMatroidInt_maxCommonCard
import Definitions.Def_AuctionMatroidInt_Supplement_StreamAlg
import Definitions.Def_AuctionMatroidInt_Supplement_StreamAlg_IsLegal

namespace AuctionMatroidInt.Supplement

/-- **Theorem 1.4 (unweighted, semi-streaming).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Theorem 1.4, p.5 (PDF p.7),
restated p.32: "Let 0 < ε < 1. For the unweighted matroid intersection problem in the
semi-streaming setting, there exists a deterministic (1−ε)-approximation algorithm using
O(1/ε²) passes, O(r) space, and O(n log(r)/ε²) independence queries." Footnote 3: "We measure
the space complexity by the number of machine words, and we assume that each machine word has
O(log n) bits."

There are absolute constants `C, c` and one legal deterministic semi-streaming algorithm `A n ε`
(built from `n` and `ε` alone) such that for every `n`, every `0 < ε < 1`, all matroids
`M₁ = ([n], I₁)`, `M₂ = ([n], I₂)` (loops allowed) and every order `σ` of the stream (each
element of `[n]` exactly once, the same order in every pass), with `r` the maximum size of a
common independent set:
1. the run halts, at some micro-step `t`, with an output `X ∈ I₁ ∩ I₂` such that
   `(1 − ε) r ≤ |X|`;
2. at most `C/ε²` passes have been started by then;
3. at most `C n log(r+2)/ε²` independence queries have been made by then;
4. at every micro-step the memory has at most `C (r + 1)` words;
5. every number ever stored is below `(n + 2)^c` (words of `O(log n)` bits).

**Formalization Note.** The model is `StreamAlg` with `StreamAlg.IsLegal` (elements are opaque,
queries touch only stored elements and the arriving element). Answers come from the published
`indepOracle`. `log r` is read as `log(r + 2)` and `O(r)` words as `C (r + 1)` words, since the
printed rates vanish at `r ≤ 1`. No assumption of §2.1 is made. -/
theorem theorem_1_4 :
    ∃ C c : ℕ, ∃ A : (n : ℕ) → ℝ → StreamAlg n,
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
        (A n ε).IsLegal ∧
        ∀ I : Fin 2 → Finset (Fin n) → Prop,
          CombOpt.MatroidPolytope.IsMatroid (I 0) → CombOpt.MatroidPolytope.IsMatroid (I 1) →
          ∀ σ : List (Fin n), σ.Nodup → (∀ e, e ∈ σ) →
            (∃ (t : ℕ) (X : Finset (Fin n)),
              ((A n ε).config (indepOracle I) σ t).out = some X ∧
              I 0 X ∧ I 1 X ∧
              (1 - ε) * (maxCommonCard (I 0) (I 1) : ℝ) ≤ X.card ∧
              (((A n ε).config (indepOracle I) σ t).passes : ℝ) ≤ C / ε ^ 2 ∧
              (((A n ε).config (indepOracle I) σ t).queries : ℝ) ≤
                C * n * Real.log (maxCommonCard (I 0) (I 1) + 2) / ε ^ 2) ∧
            ∀ s : ℕ,
              ((A n ε).config (indepOracle I) σ s).mem.length ≤
                C * (maxCommonCard (I 0) (I 1) + 1) ∧
              ∀ k : ℕ, Cell.num k ∈ ((A n ε).config (indepOracle I) σ s).mem →
                k < (n + 2) ^ c := by sorry

end AuctionMatroidInt.Supplement
