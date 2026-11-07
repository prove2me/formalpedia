-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_4_12
-- name    : BFAlmostLinear.lemma_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:40.781942+00:00
-- url     : https://prove2.me/theorems/d46133b7-ca6e-49e0-8ac2-2f39b8153c26
-- title:
--   Lemma 4.12 and Theorem 4.1 (2) — shortcuts remove $\lfloor h/3\rfloor$ of $h$ negative hops
-- statement:
--   Let $G$ be a weighted graph with frozen flags satisfying (I1), $\phi$ a valid potential, $\Delta:V\to\mathbb R$, and $G'$ the graph $G_\phi$ with shortcut arcs (S1)–(S5) built from $\Delta$. The negative arcs of $G'$ are the frozen arcs of $G$ and the (S4), (S5) arcs.
--
--   1. **(Lemma 4.12.)** For all $a,b\in V$ and every real walk $P$ from $a$ to $b$ in $G_\phi$ of weight $d_{G_\phi}(a,b)$ with $h$ negative arcs, there is a walk from $a$ to $b$ in $G'$ of the same weight with at most $h-\lfloor h/3\rfloor$ negative arcs.
--   2. **(Theorem 4.1, item 2.)** For all $s,t\in V$ and every hop bound $h$,
--   $$d^{\,h-\lfloor h/3\rfloor}_{G'}(s,t)\le d^h_G(s,t)+\phi(s)-\phi(t).$$
--
--   Iterating this $O(\log n)$ times leaves shortest paths with at most two negative hops.
--
--   Differences from the source:
--   - generalization: Lemma 4.12 → also Theorem 4.1, item 2 as a conjunct; reason: it is the form the proof of Theorem 1.1 uses; dropping it gives the lemma.
--   - generalization: $\Delta_r$ from Lemma 4.8 → any real $\Delta$ with the printed clamp; reason: the case analysis does not use where $\Delta$ comes from.
--   - reading: "$G'$ has shortcut edges (S1)–(S5)" → $G'=G_\phi$ plus (S1)–(S5), without (S6) and before the final Lemma 1.2; reason: (S6) is auxiliary, and Lemma 1.2 keeps $d^h$ by item 1.
--   - reading: "path", "shortest" → walk, of weight $d_{G_\phi}(a,b)$; reason: §1.1 distances; walks agree with paths when no negative cycle is on them.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 4.12, p.25; Theorem 4.1, item 2, p.12

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_shortcut

namespace BFAlmostLinear

/-- **Lemma 4.12**, p.25. "Consider any a, b ∈ V and any shortest (a, b)-path P in G_ϕ with h negative edges. If G′ has
shortcut edges (S1)–(S5), then there is an (a, b)-path in G′ with weight d_{G_ϕ}(a, b) and with at most h − ⌊h/3⌋ negative
edges." With Theorem 4.1, item 2, p.12: "For any s, t ∈ V and hop bound h, we have d^{h−⌊h/3⌋}_{G′}(s, t) ≤
d^h_G(s, t) + ϕ(s) − ϕ(t)", which is the form that the proof of Theorem 1.1 uses.

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.12, p.25 and Theorem 4.1, item 2, p.12.

**Formalization Note.** `G′` is `shortcut (G_ϕ) Δ`, for any real `Δ`. Its hops are the frozen arcs of `G` and all (S4)–(S5) arcs;
(S2)–(S3) arcs count no hop. Natural subtraction is safe since `⌊h/3⌋ ≤ h`. "Shortest" means that the weight of `P` is `d_{G_ϕ}(a, b)`.
The application of Lemma 1.2 on p.24, which keeps `d^h` by item 1, is not part of `G′`. -/
theorem lemma_4_12 {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (hI1 : G.I1)
    (ϕ : V → ℝ) (hϕ : G.IsValid ϕ) (Δ : V → ℝ) :
    (∀ (a b : V) (P : List E), (G.reweight ϕ).IsRealWalk a b P →
      ((pathWeight (G.reweight ϕ).w P : ℝ) : EReal) = (G.reweight ϕ).dist a b →
      ∃ Q, ((G.reweight ϕ).shortcut Δ).IsRealWalk (Sum.inl a) (Sum.inl b) Q ∧
        pathWeight ((G.reweight ϕ).shortcut Δ).w Q = pathWeight (G.reweight ϕ).w P ∧
        ((G.reweight ϕ).shortcut Δ).hops Q ≤ G.hops P - G.hops P / 3) ∧
    (∀ (h : ℕ) (s t : V),
      ((G.reweight ϕ).shortcut Δ).dH (h - h / 3) (Sum.inl s) (Sum.inl t) ≤
        G.dH h s t + ((ϕ s - ϕ t : ℝ) : EReal)) := by sorry

end BFAlmostLinear
