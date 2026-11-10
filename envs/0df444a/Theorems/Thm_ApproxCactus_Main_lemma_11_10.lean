-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_11_10
-- name    : ApproxCactus.Main.lemma_11_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:01:59.002498+00:00
-- url     : https://prove2.me/theorems/76baba71-8ed7-48b3-aa18-d256bcb1bffd
-- title:
--   Lemma 11.10 — a β-broad k-separation with a side of more than α′ vertices keeps more than α of them in the torso
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph, $\beta>\beta_{11.5}(q,k)=4q+k$, $\alpha\in\mathbb N$ and $\alpha'\ge\alpha'_{11.10}(q,k,\alpha):=q\cdot\binom{\alpha}{\le k-1}+\alpha$. Let $\sigma$ be a star of $(\beta,k)$-irrelevant separations of $G$ with torso $Z$, and $s=(A,B)$ a $\beta$-broad separation of $G$ of order exactly $k$ with $|A|>\alpha'$. Then $|A\cap V(Z)|>\alpha$.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: (n choose ⩽ k − 1) = Σ_{i=0}^{k−1} (n choose i) → chooseBelow n k = Σ_{i < k} n.choose i; reason: the same sum; for k = 0 both are the empty sum 0
--   - encoding: the torso Z of σ, a graph on ⋂ B_i, and lifts (Definition 9.23) → torso G σ : SimpleGraph on the subtype of torsoVerts σ; IsLift G σ s ŝ with s a separation of the torso and ŝ of G, A = Â ∩ V(Z), B = B̂ ∩ V(Z), sep(s) = sep(ŝ); reason: vertices of Z are vertices of G; the subtype makes Z a graph in its own right so that separations of Z are defined by the same predicate
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 11.10, printed p. 116 (PDF p. 119)

import Definitions.Def_ApproxCactus_Main_Torso

namespace ApproxCactus.Main

/-- **Lemma 11.10**, p. 116: let `G` be `(q, k − 1)`-unbreakable, `β > 4q + k`, `α ∈ ℕ` and
`α' ⩾ α'11.10(q, k, α) := q · (α choose ⩽ k − 1) + α`. Let `σ` be a star of `(β, k)`-irrelevant
separations with torso `Z`, and `s = (A, B)` a `β`-broad `k`-separation with `|A| > α'`. Then
`|A ∩ V(Z)| > α`. -/
theorem lemma_11_10 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k β α α' : ℕ)
    (hG : IsUnbreakableBelow G q k) (hβ : 4 * q + k < β)
    (hα' : q * chooseBelow α k + α ≤ α')
    (σ : Set (Finset V × Finset V)) (hσ : IsStar σ) (hirr : ∀ t ∈ σ, IsIrrelevant G β k t)
    (s : Finset V × Finset V) (hs : IsSep G s) (hsk : order s = k) (hsb : β ≤ breadth s)
    (hA : α' < s.1.card) :
    α < (s.1 ∩ torsoVerts σ).card := by sorry

end ApproxCactus.Main
