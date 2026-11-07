-- Prove2me | Theorems.Thm_BFAlmostLinear_subclaim_4_9
-- name    : BFAlmostLinear.subclaim_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:46.719263+00:00
-- url     : https://prove2.me/theorems/128f6bf3-52ec-4603-8091-9510f436475a
-- title:
--   Subclaim 4.9 with (1), (2) — $h$-hop searches in $G$ are 1-hop searches in the layered graph $H$
-- statement:
--   Let $G$ be a weighted graph with frozen flags, $h\ge0$, and $H$ the reweighted layered graph of Lemma 4.8 with potential $\phi$. Weights and hops of walks of $G$ are those of $G$, auxiliary arcs allowed. Then:
--
--   1. every arc of $H$ other than the arcs $r^{\mathrm{tail}}\to r^{\mathrm{head}}$ has non-negative weight;
--   2. $d_H(u^{\mathrm{out}}_0,v^{\mathrm{out}}_i)=\tilde d^{\,i}(u,v)+\phi(u^{\mathrm{out}}_0)-\phi(v^{\mathrm{out}}_i)$ for $0\le i\le h+1$ (display (1));
--   3. $d_H(u^{\mathrm{in}}_i,v^{\mathrm{in}}_0)=\tilde d^{\,i}(u,v)+\phi(u^{\mathrm{in}}_i)-\phi(v^{\mathrm{in}}_0)$ for $0\le i\le h$ (display (2));
--   4. for every vertex $u$, negative vertex $r$ and real $\Delta_r$: $u$ is on a walk of at most $h+1$ hops starting at $r$ of weight $<-\Delta_r$ if and only if $d_H(r^{\mathrm{tail}},u^{\mathrm{out}}_i)<-\Delta_r+\phi(r^{\mathrm{tail}})$ for some $i\in\{0,\dots,h+1\}$; and $u$ is on a walk of at most $h$ hops ending at $r$ of weight $<\Delta_r$ if and only if $d_H(u^{\mathrm{in}}_i,r^{\mathrm{tail}})<\Delta_r-\phi(r^{\mathrm{tail}})$ for some $i\in\{0,\dots,h\}$.
--
--   This turns the $h$-hop searches of Lemma 4.8 into the 1-hop searches of Lemma 4.6.
--
--   Differences from the source:
--   - generalization: Subclaim 4.9 alone → also the non-negativity bullets of p.20 and displays (1), (2) of p.21 as conjuncts; reason: they are the facts the subclaim rests on; dropping them gives the printed subclaim.
--   - generalization: $\Delta_r$ computed by the algorithm, $G$ with (I1) → any real $\Delta_r$ and no (I1); reason: the equivalences hold for every value and do not use (I1).
--   - reading: "$u$ is on an $(h+1)$-hop path of total weight less than $-\Delta_r$ that starts from $r$" → $u$ is a vertex of a walk from $r$ with at most $h+1$ hops and total weight $<-\Delta_r$, auxiliary arcs allowed; reason: walks, as $\tilde d$ is defined on walks (§3, p.10), and the proof's equivalence uses the whole walk's weight.
--   - encoding: frozen flags → hypothesis `Frozen`; reason: keeps the potential of $H$ finite (§1.1).
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), proof of Lemma 4.8, p.20 (non-negativity bullets), Subclaim 4.9, pp.20–21, displays (1), (2), p.21

import Mathlib
import Definitions.Def_BFAlmostLinear_layeredH

namespace BFAlmostLinear

/-- **Subclaim 4.9**, pp.20–21, with displays (1), (2), p.21 and the bullets on p.20. "For any vertex u and any negative
vertex r, • u is on an (h + 1)-hop path of total weight less than −∆_r that starts from r if and only if there exists some
i ∈ {0, 1, …, h + 1} such that d_H(r_tail, u^out_i) < −∆_r + ϕ(r_tail). • u is on an h-hop path of total weight less than ∆_r
that ends at r if and only if there exists some i ∈ {0, 1, …, h} such that d_H(u^in_i, r_tail) < ∆_r − ϕ(r_tail)."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Subclaim 4.9, pp.20–21.

**Formalization Note.** `H` is the explicit `layeredH G h`, and `∆` any real. The weight and the hops of a walk are those
of `G`, before `H`'s reweighting; walks may use auxiliary arcs of `G`, and the hop count is the frozen flags. "u is on a path" is
a walk through `u` under the hop limit. Neither (I1) nor validity is needed; only `Frozen`, which keeps the potential of `H`
finite. Clauses: every arc of `H` other than `(v_tail, v_head)` is nonnegative; then (1) and (2); then the two equivalences. -/
theorem subclaim_4_9 {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (h : ℕ)
    (hF : G.Frozen) :
    (∀ a : HArc G h, (∀ r, a ≠ HArc.gMid r) → 0 ≤ (layeredH G h).w a) ∧
    (∀ (i : Fin (h + 2)) (u v : V),
      (layeredH G h).dist (.out 0 u) (.out i v) =
        G.dHt i u v + ((layeredPot G h (.out 0 u) - layeredPot G h (.out i v) : ℝ) : EReal)) ∧
    (∀ (i : Fin (h + 1)) (u v : V),
      (layeredH G h).dist (.inn i u) (.inn 0 v) =
        G.dHt i u v + ((layeredPot G h (.inn i u) - layeredPot G h (.inn 0 v) : ℝ) : EReal)) ∧
    (∀ (r : G.NegVertex) (u : V) (Δ : ℝ),
      ((∃ (t : V) (P : List E), G.net.IsPathFrom r.1 t P ∧ G.hops P ≤ h + 1 ∧
          G.Visits r.1 P u ∧ pathWeight G.w P < -Δ) ↔
        ∃ i : Fin (h + 2), (layeredH G h).dist (.tl r) (.out i u) <
          ((-Δ + layeredPot G h (.tl r) : ℝ) : EReal)) ∧
      ((∃ (s : V) (P : List E), G.net.IsPathFrom s r.1 P ∧ G.hops P ≤ h ∧
          G.Visits s P u ∧ pathWeight G.w P < Δ) ↔
        ∃ i : Fin (h + 1), (layeredH G h).dist (.inn i u) (.tl r) <
          ((Δ - layeredPot G h (.tl r) : ℝ) : EReal))) := by sorry

end BFAlmostLinear
