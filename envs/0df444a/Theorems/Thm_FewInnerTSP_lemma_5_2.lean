-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_5_2
-- name    : FewInnerTSP.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:34:03.652106+00:00
-- url     : https://prove2.me/theorems/c5ce1cf3-e478-42be-9c73-eb391ebf8d2e
-- title:
--   Lemma 5.2 (Representative families on a fixed terminal set)
-- statement:
--   Let $S$ be a well-formed state with an even number $b=|B|>0$ of terminals.
--
--   1. For every finite family $\mathcal A$ of feasible covers of $S$ and every injective tie rule, the weighted rank reduction $\mathcal R$ of $\mathcal A$ (App. C.1) is a subfamily of $\mathcal A$ with $|\mathcal R|\le2^{b-1}$, and it preserves the minimum attainable weight for every external matching: for every perfect matching $X$ on $B$ and every $C\in\mathcal A$ with $M(C)\cup X$ connected there is $R\in\mathcal R$ with $w(R)\le w(C)$ and $M(R)\cup X$ connected.
--   2. There are an admissible real-RAM program and a constant $C$, fixed before the input, which, given $b$ and $N$ rows, each a weight and a perfect matching on the $b$ terminals, halt within
--   $$C\,(N+1)\bigl(\log(N+2)+2^{Cb}\bigr)$$
--   steps and output the indicator of a set of at most $2^{b-1}$ rows with the same preservation property.
--
--   This is the compression that keeps the number of stored representatives single-exponential in the number of terminals.
--
--   **Formalization Note** A cover enters the operation only through its weight and its matching. The $\log$ term charges the sorting of the weights, which the printed count lists separately.
--
--   Differences from the source:
--   - generalization: any finite family can be replaced by a family of at most 2^{b−1} covers → the weighted rank reduction of App. C.1, for every injective tie rule, is such a subfamily; reason: the explicit reduction is what the page's proof and Algorithm 2 use, and it implies the existence claim
--   - generalization: covers of a state on the fixed skeleton → covers of a well-formed state on any skeleton Γ; reason: the rank argument reads only the matchings on B; it specializes to the fixed skeleton
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: |A| 2^{O(b)} operations, in addition to the cost of reading and ordering the supplied weights → (T+1) ≤ C (N+1) (log(N+2) + 2^{Cb}), the reading and sorting included; reason: on this machine every instruction is charged, so the additional costs are written out; N+1 instead of N, which is within a factor 2 for N ≥ 1, because the machine takes at least one step on the empty family
--   - encoding: a family of covers of a state → rows of (weight, partner function of a perfect matching on Fin b), output the 0/1 indicator of the retained rows; reason: the operation reads only weights and matchings
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 5.2, p.10 (PDF p.12); proof App. C.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_FewInnerTSP_RankReduction
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

/-- **Lemma 5.2 (Representative families on a fixed terminal set).** Li, Ma, Gong, *Exact Euclidean TSP
with Few Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…),
Lemma 5.2, p.10 (PDF p.12), proof App. C.1, p.19 (PDF p.21): "For even b = |B| > 0, any finite family A
of feasible covers of the same state can be replaced by a family of at most 2^{b−1} covers that preserves
the minimum attainable weight for every external matching. The operation uses |A|2^{O(b)} arithmetic and
bit operations, in addition to the cost of reading and ordering the supplied weights."

1. For a well-formed state `S` on a skeleton `Γ` with `b = |B|` even and positive, every finite family
   `𝒜` of feasible covers of `S`, and every injective tie rule: the weighted rank reduction of App. C.1
   (`rankReduce`) is a subfamily of `𝒜` with at most `2^{b−1}` members, and for every external matching
   `X` (a perfect matching on `B`) and every `C ∈ 𝒜` with `M(C) ∪ X` connected there is a retained `R`
   with `w(R) ≤ w(C)` and `M(R) ∪ X` connected.
2. One admissible program and a constant `C`, fixed before the input, given `b` (even, positive) and a
   list of `N` rows, each a weight and a perfect matching on `b` terminals (as a partner function), halt
   within `C (N + 1) (log(N + 2) + 2^{C b})` steps and output the `0/1` indicator of a set of at most `2^{b−1}`
   rows such that for every perfect matching `X` and every row `i` compatible with `X` some retained row
   `j` is compatible with `X` and has weight at most that of `i`.

**Formalization Note** The `log` term charges the sorting of the weights, which the printed count leaves
"in addition to"; every executed instruction costs `1` on this machine. The factor is `N + 1`, not `N`: the
machine takes at least one step, so `N` would make the bound `0` and the clause false on the empty list. In clause 2 a cover is represented
by its weight and its induced matching, which is all the operation reads. -/
theorem lemma_5_2 :
    (∀ (n m : ℕ) (Γ : Skeleton n m) (S : State n m), IsState Γ S → 0 < S.B.card → Even S.B.card →
      ∀ (tie : Finset (Edge n m) → ℕ), Function.Injective tie →
      ∀ 𝒜 : Finset (Finset (Edge n m)), (∀ C ∈ 𝒜, IsFeasibleCover Γ S C) →
        rankReduce Γ S tie 𝒜 ⊆ 𝒜 ∧ (rankReduce Γ S tie 𝒜).card ≤ 2 ^ (S.B.card - 1) ∧
        ∀ X : Finset (Sym2 (Fin n)), IsPerfectMatching S.B X → ∀ C ∈ 𝒜,
          Compatible S.B (matchingOf Γ S C) X →
          ∃ R ∈ rankReduce Γ S tie 𝒜, S.wtOf R ≤ S.wtOf C ∧
            Compatible S.B (matchingOf Γ S R) X) ∧
    (∃ Prog : MatMulTimeLP.Program, Admissible Prog ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (b : ℕ), 0 < b → Even b → ∀ rows : List (ℝ × (Fin b → Fin b)), (∀ r ∈ rows, IsPartner r.2) →
      ∀ ω : MatMulTimeLP.Tape, ∃ (T : ℕ) (keep : Fin rows.length → Bool),
        MatMulTimeLP.HaltsAt Prog (repLayout rows) ω T ∧
        (T : ℝ) + 1 ≤ C * ((rows.length : ℝ) + 1) *
          (Real.log ((rows.length : ℝ) + 2) + (2 : ℝ) ^ (C * (b : ℝ))) ∧
        OutputIs Prog (repLayout rows) ω T (List.ofFn fun i => if keep i then (1 : ℝ) else 0) ∧
        (Finset.univ.filter fun i => keep i = true).card ≤ 2 ^ (b - 1) ∧
        ∀ X : Fin b → Fin b, IsPartner X → ∀ i : Fin rows.length,
          Compatible Finset.univ (partnerPairs (rows.get i).2) (partnerPairs X) →
          ∃ j : Fin rows.length, keep j = true ∧ (rows.get j).1 ≤ (rows.get i).1 ∧
            Compatible Finset.univ (partnerPairs (rows.get j).2) (partnerPairs X)) := by sorry

end FewInnerTSP
