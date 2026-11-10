-- Prove2me | Theorems.Thm_ApproxCactus_Main_key_lemma_6_6
-- name    : ApproxCactus.Main.key_lemma_6_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:03:10.605424+00:00
-- url     : https://prove2.me/theorems/ed971bbc-9d6f-4c43-aee6-d677fd48a1ed
-- title:
--   Key Lemma 6.6 (Flower Approximation Lemma) — nontrivial asteriskal sets of broad narrow k-separations are approximated by a canonical q-lean graphic-k-flower
-- statement:
--   For all $q,k\in\mathbb N$ there are $\beta_{6.6}\ge q$, $\gamma_{6.6}$ and $\varepsilon_{6.6}$ in $\mathbb N$ such that the following holds. Let $G$ be a finite $(q,k-1)$-unbreakable graph and $\gamma>\gamma_{6.6}$. There is an assignment $S\mapsto F(S)=F_{6.6}(S)$ of a graph-decomposition of $G$ to each set of separations such that for every nontrivial $\gamma$-asteriskal set $S$ of $\beta_{6.6}$-broad narrow separations of $G$ of order exactly $k$, $F(S)$ is a $q$-lean graphic-$k$-flower and:
--   (i) every separation in $S$ has edit-distance $\le\varepsilon_{6.6}$ to some displayed separation of $F(S)$;
--   (ii) for every $\varepsilon\ge\varepsilon_{6.6}$, every separation of order $k$ that is $\varepsilon$-compatible with $F(S)$ is $\varepsilon$-nested with all petal-separations of $F(S)$;
--   (iii) if $F(S)$ is a graphic-$k$-daisy, it has the clover-property;
--   (iv) $F$ is canonical: for every automorphism $\psi$ of $G$, $F(S)$ and $F(\psi(S))$ are $\psi$-isomorphic.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: graph-decomposition (H, V) with H a strong cactus, a cycle Z_ℓ or a star, and designated P-nodes → Decomp G: a finite loopless multigraph (node type, edge type, endpoint map), bags as Finsets, a set of P-nodes, (H1) and (H2); reason: cacti, cycles and stars are loopless; parallel edges are kept so that Z_2 is a 2-cycle; any finite multigraph can be relabelled by types in Type
--   - reading: "Then there is a q-lean graphic-k-flower F := F6.6(S)" with (iv) comparing F6.6(S) and F6.6(ψ(S)) → an assignment F : Set (Finset V × Finset V) → Decomp G chosen after G and γ, satisfying all clauses for every admissible S; reason: clause (iv) compares the flowers of S and ψ(S), so the flower is a function of S (for fixed G and γ); its value on other sets is irrelevant
--   - reading: star-decomposition (Definition 3.9) → the decomposition multigraph is a star K_{1,n} (n ≥ 0) with designated centre c: every edge at c, no parallel edges, every other node joined to c; reason: the standard meaning of a star; the paper places no lower bound on the number of leaves
--   - reading: "the node of O corresponding to t" in γ-compatibility with a daisy → the daisy clauses are required at every node p whose petal-separation is γ-crossed, for the two edges e ≠ f at p; reason: each petal-separation is indexed by its node; this is the literal per-node reading
--   - encoding: an isomorphism φ: V(H) → V(H′) of decomposition graphs (Definition 6.5) → a node bijection together with a compatible edge bijection of the multigraphs; reason: this is graph isomorphism for multigraphs; for the simple star it is equivalent to a node isomorphism
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Key Lemma 6.6, printed p. 46 (PDF p. 49)

import Definitions.Def_ApproxCactus_Main_Flowers

namespace ApproxCactus.Main

/-- **Key Lemma 6.6 (Flower Approximation Lemma)**, p. 46. For all `q, k` there are constants
`β6.6 ≥ q`, `γ6.6`, `ε6.6` such that for every `(q, k − 1)`-unbreakable `G` and every `γ > γ6.6`
there is an assignment `S ↦ F6.6(S)` of a decomposition of `G` to each set of separations, such
that for every nontrivial `γ`-asteriskal set `S` of `β6.6`-broad narrow `k`-separations of `G`,
`F6.6(S)` is a `q`-lean graphic-`k`-flower with
(i) every `s ∈ S` at edit-distance `⩽ ε6.6` from a displayed separation of `F6.6(S)`;
(ii) for every `ε ≥ ε6.6`, every `k`-separation `ε`-compatible with `F6.6(S)` is `ε`-nested with
all petal-separations of `F6.6(S)`;
(iii) if `F6.6(S)` is a graphic-`k`-daisy, it has the clover-property;
(iv) canonicity: for every automorphism `ψ` of `G`, `F6.6(S)` and `F6.6(ψ(S))` are
`ψ`-isomorphic. -/
theorem key_lemma_6_6 (q k : ℕ) :
    ∃ β₀ γ₀ ε₀ : ℕ, q ≤ β₀ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        IsUnbreakableBelow G q k → ∀ γ : ℕ, γ₀ < γ →
        ∃ F : Set (Finset V × Finset V) → Decomp G,
          ∀ S : Set (Finset V × Finset V),
            IsAsteriskal γ S → ¬ IsTrivialSet S →
            (∀ s ∈ S, IsSep G s ∧ order s = k ∧ β₀ ≤ breadth s ∧ IsNarrow G s) →
            IsGraphicFlower G k (F S) ∧ IsQLean G q k (F S) ∧
            (∀ s ∈ S, ∃ t, (F S).IsDisplayed t ∧ EditDistLe ε₀ s t) ∧
            (∀ ε : ℕ, ε₀ ≤ ε → ∀ s : Finset V × Finset V, IsSep G s → order s = k →
              IsCompatible G k ε (F S) s → ∀ p : (F S).N, NestedEps ε s ((F S).petalSep p)) ∧
            (IsGraphicDaisy G k (F S) → HasClover k (F S)) ∧
            (∀ ψ : G ≃g G, PsiIso ψ (F S) (F (mapSepSet ψ S))) := by sorry

end ApproxCactus.Main
