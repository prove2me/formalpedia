-- Prove2me | Theorems.Thm_ApproxCactus_Main_lemma_11_12
-- name    : ApproxCactus.Main.lemma_11_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:02:08.06595+00:00
-- url     : https://prove2.me/theorems/b936ce49-9102-4315-aad6-75591c25e8ac
-- title:
--   Lemma 11.12 — lifts of γ-close (⩽k)-separations of the torso are δ11.11(q, k, γ)-close
-- statement:
--   Let $G$ be a finite $(q,k-1)$-unbreakable graph and $\beta>q$. Let $\gamma\in\mathbb N$ and $\delta\ge\delta_{11.12}(q,k,\gamma):=\delta_{11.11}(q,k,\gamma)=\max\{\gamma+q\binom{k+\gamma}{\le k-1},3q+k-1\}$. Let $\sigma$ be a star of $(\beta,k)$-irrelevant separations of $G$ with torso $Z$, $s,t$ two $\gamma$-close separations of $Z$ of order $\le k$, and $\hat s$, $\hat t$ lifts of $s$, $t$. Then $\hat s$ and $\hat t$ are $\delta$-close.
--
--   Differences from the source:
--   - reading: a graph (unqualified) → a finite simple graph G : SimpleGraph V on a Fintype V with DecidableEq V; reason: the paper says "infinite graph" explicitly whenever it means one (the covering of §6); the unqualified graphs in these statements are taken to be finite
--   - encoding: a separation (A, B) of G → a pair (A, B) : Finset V × Finset V with IsSep G (A ∪ B = V(G), no edge between A ∖ B and B ∖ A); reason: the same objects; the predicate selects which pairs are separations
--   - encoding: (q, k − 1)-unbreakable: every separation of order at most k − 1 has breadth ≤ q → IsUnbreakableBelow G q k: every separation of order < k has breadth ≤ q; reason: identical for k ≥ 1; for k = 0 both are vacuous (no truncated natural subtraction k − 1)
--   - encoding: (n choose ⩽ k − 1) = Σ_{i=0}^{k−1} (n choose i) → chooseBelow n k = Σ_{i < k} n.choose i; reason: the same sum; for k = 0 both are the empty sum 0
--   - encoding: ν11.7(q, k) − 1 = 3q + k − 1 (an integer) → 3 * q + k - 1 in ℕ (truncated); reason: differs only at q = k = 0 (0 instead of −1), where the max with γ + … ≥ 0 is unchanged
--   - encoding: the torso Z of σ, a graph on ⋂ B_i, and lifts (Definition 9.23) → torso G σ : SimpleGraph on the subtype of torsoVerts σ; IsLift G σ s ŝ with s a separation of the torso and ŝ of G, A = Â ∩ V(Z), B = B̂ ∩ V(Z), sep(s) = sep(ŝ); reason: vertices of Z are vertices of G; the subtype makes Z a graph in its own right so that separations of Z are defined by the same predicate
-- source:
--   Bourneuf, Carmesin, Kurkofka and Planken, An approximate cactus-decomposition for vertex-connectivity, arXiv:2611.01772 (held PDF sha256 78b7d09a…), Lemma 11.12, printed p. 116 (PDF p. 119)

import Definitions.Def_ApproxCactus_Main_Torso

namespace ApproxCactus.Main

/-- **Lemma 11.12**, p. 116: let `G` be `(q, k − 1)`-unbreakable, `β > q`, `γ ∈ ℕ` and
`δ ⩾ δ11.12(q, k, γ) := δ11.11(q, k, γ) = max{γ + q · (k + γ choose ⩽ k − 1), 3q + k − 1}`. Let `σ`
be a star of `(β, k)`-irrelevant separations with torso `Z`, `s, t` two `γ`-close
`(⩽ k)`-separations of `Z`, and `ŝ, t̂` lifts of `s, t`. Then `ŝ` and `t̂` are `δ`-close. -/
theorem lemma_11_12 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (q k β γ δ : ℕ)
    (hG : IsUnbreakableBelow G q k) (hβ : q < β)
    (hδ : max (γ + q * chooseBelow (k + γ) k) (3 * q + k - 1) ≤ δ)
    (σ : Set (Finset V × Finset V)) (hσ : IsStar σ) (hirr : ∀ r ∈ σ, IsIrrelevant G β k r)
    (s t : Finset {v : V // v ∈ torsoVerts σ} × Finset {v : V // v ∈ torsoVerts σ})
    (hs : IsSep (torso G σ) s) (ht : IsSep (torso G σ) t) (hsk : order s ≤ k) (htk : order t ≤ k)
    (hclose : Close γ s t)
    (sHat tHat : Finset V × Finset V) (hsHat : IsLift G σ s sHat) (htHat : IsLift G σ t tHat) :
    Close δ sHat tHat := by sorry

end ApproxCactus.Main
