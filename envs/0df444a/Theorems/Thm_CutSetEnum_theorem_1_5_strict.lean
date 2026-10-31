-- Prove2me | Theorems.Thm_CutSetEnum_theorem_1_5_strict
-- name    : CutSetEnum.theorem_1_5_strict
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:14:31.453238+00:00
-- url     : https://prove2.me/theorems/60693b64-fd69-4f56-a106-deb4809e1f9e
-- title:
--   Theorem 1.5, conclusion 2 — strict partition uncrossing
-- statement:
--   Let $G=(V,E)$ be a hypergraph, $k\ge2$ an integer and $\emptyset\ne R\subsetneq U\subsetneq V$. Let $S=\{u_1,\dots,u_p\}\subseteq U\setminus R$ be $p\ge 2k-2$ distinct vertices. For each $i\in[p]$ let $(\bar A_i,A_i)$ be a minimum $((S\cup R)\setminus\{u_i\},\bar U)$-terminal cut (so $\bar A_i$ is the source side), and suppose $u_i\in A_i\setminus\bigcup_{j\ne i}A_j$ for every $i$. Put
--   $$
--   W=\bigcup_{1\le i<j\le p}(A_i\cap A_j),\qquad Z=\bigcap_{i\in[p]}\bar A_i .
--   $$
--   If some hyperedge $e\in E$ meets $W$, meets $Z$ and is contained in $W\cup Z$, then there is a $k$-partition $(P_1,\dots,P_k)$ of $V$ with $\bar U\subsetneq P_k$ such that
--   $$
--   |\delta(P_1,\dots,P_k)|<\tfrac12\min\{d(A_i)+d(A_j):\ i,j\in[p],\ i\ne j\}.
--   $$
--
--   Conclusion 1 of the same theorem (the non-strict inequality, without the hyperedge $e$) is the published `HyperKCut.Structure.theorem_3_1`. The strict form is what the proof of Lemma 2.1 uses to produce a $k$-partition cheaper than $OPT_{k\text{-cut}}$. The paper cites it from Beideman, Chandrasekaran and Wang (SODA 2022, reference [7]) and does not prove it.
--
--   **Formalization Note** The hypotheses are copied from `theorem_3_1`; `A i` is the sink side $A_i$ and the source side is `(A i)ᶜ`. The bound $<\frac12\min$ is written as $2\,|\delta(P)|<d(A_i)+d(A_j)$ for all $i\ne j$. $P_k$ is `P ⟨k-1, _⟩`.
--
--   Differences from the source:
--   - reading: “the inequality in the previous conclusion is strict” → one k-partition P with Ū ⊊ P_k satisfies the strict bound; reason: the strict claim is about the partition of conclusion 1, which carries Ū ⊊ P_k; this is how Lemma 2.1's proof uses it
--   - encoding: |δ(P)| < ½ min{d(Aᵢ) + d(Aⱼ) : i ≠ j} → ∀ i ≠ j, 2 · cost H P < d(Aᵢ) + d(Aⱼ); reason: equivalent; the minimum is over a non-empty finite set since p ≥ 2
--   - encoding: S = {u₁, …, u_p}, indices 1…p; W and Z defined in the statement → injective u : Fin p → V (0-based); W, Z binders pinned by equations hW, hZ; reason: relabelling; same sets
--   - encoding: (A, Ā) an (S, T)-terminal cut, a 2-partition with S ⊆ A ⊆ V \ T → published IsTerminalCut S T A := S ⊆ A ∧ Disjoint A T (no separate 2-partition clause); reason: for non-empty S and T the two coincide
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, Theorem 1.5 (conclusion 2), p.10 (PDF 11), cited from [7]

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Theorem 1.5, conclusion 2 (strict partition uncrossing).**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, Theorem 1.5, p.10 (PDF 11), cited there
from [7] (Beideman, Chandrasekaran & Wang, SODA 2022); this paper does not prove it:
"Let G = (V, E) be a hypergraph, k ≥ 2 be an integer and ∅ ≠ R ⊊ U ⊊ V. Let
S = {u₁, …, u_p} ⊆ U \ R for p ≥ 2k − 2. Let (Āᵢ, Aᵢ) be a minimum ((S ∪ R) \ {uᵢ}, Ū)-terminal
cut. Suppose that uᵢ ∈ Aᵢ \ (∪_{j∈[p]\{i}} Aⱼ) for every i ∈ [p]. Then, the following two hold:
1. There exists a k-partition (P₁, …, P_k) of V with Ū ⊊ P_k such that
|δ(P₁, …, P_k)| ≤ ½ min{d(Aᵢ) + d(Aⱼ) : i, j ∈ [p], i ≠ j}.
2. Moreover, if there exists a hyperedge e ∈ E such that e intersects W := ∪_{1≤i<j≤p}(Aᵢ ∩ Aⱼ),
e intersects Z := ∩_{i∈[p]} Āᵢ, and e is contained in W ∪ Z, then the inequality in the previous
conclusion is strict."

This is conclusion 2. The hypotheses are exactly those of the published
`HyperKCut.Structure.theorem_3_1` (conclusion 1), plus the hyperedge `e`.

**Formalization Note.** `A i` is the sink side `Aᵢ`; the source side `Āᵢ` is `(A i)ᶜ`, so
`IsMinTerminalCut H ((S ∪ R) \ {u i}) Uᶜ (A i)ᶜ`. Indices are `Fin p` (0-based); `u` is
injective, so `S` has exactly `p` elements. The k-partition is `P : Fin k → Finset V` with last
part `P ⟨k - 1, _⟩ = P_k`. The bound `|δ(P)| < ½ min{d(Aᵢ) + d(Aⱼ) : i ≠ j}` is written
`2 · cost H P < d(Aᵢ) + d(Aⱼ)` for all `i ≠ j` (the minimum is over a non-empty finite set since
`p ≥ 2`). "The inequality is strict" means: one k-partition with `Ū ⊊ P_k` satisfies the strict
bound. `W` and `Z` are binders pinned by `hW` and `hZ`. -/
theorem theorem_1_5_strict (H : HyperKCut.Structure.Hypergraph V) (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hUV : U ⊂ (Finset.univ : Finset V))
    (u : Fin p → V) (huinj : Function.Injective u)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j)
    (W Z : Finset V)
    (hW : W = (Finset.univ.filter (fun ij : Fin p × Fin p => ij.1 < ij.2)).biUnion
        (fun ij => A ij.1 ∩ A ij.2))
    (hZ : Z = Finset.univ.inf (fun i => (A i)ᶜ))
    (e : Finset V) (he : e ∈ H.edges)
    (heW : Meets e W) (heZ : Meets e Z) (heWZ : e ⊆ W ∪ Z) :
    ∃ P : Fin k → Finset V, IsPartition P ∧
      Uᶜ ⊂ P ⟨k - 1, by omega⟩ ∧
      ∀ i j : Fin p, i ≠ j → 2 * cost H P < d H (A i) + d H (A j) := by sorry

end CutSetEnum
