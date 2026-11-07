-- Prove2me | Theorems.Thm_BFAlmostLinear_claim_4_10
-- name    : BFAlmostLinear.claim_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:03.842091+00:00
-- url     : https://prove2.me/theorems/c22661b6-5c8d-4f36-a55f-96c6d28bc3ca
-- title:
--   Claim 4.10 — shortcut arcs (S1)–(S5) preserve distances: $d_{G'}=d_{G_\phi}=d_G+\phi(s)-\phi(t)$
-- statement:
--   Let $G$ be a weighted graph with frozen flags satisfying (I1). For every valid potential $\phi$ and every $\Delta:V\to\mathbb R$, let $G'$ be $G_\phi$ with the shortcut arcs (S1)–(S5) built from $\Delta$. Then for all $s,t\in V$
--   $$d_{G'}(s,t)=d_{G_\phi}(s,t),$$
--   and for every potential $\phi$ and all $s,t$,
--   $$d_{G_\phi}(s,t)=d_G(s,t)+\phi(s)-\phi(t).$$
--   Distances are over real arcs and take values in $\mathbb R\cup\{\pm\infty\}$.
--
--   Adding the shortcut arcs never shortens a distance, so shortcutting is safe.
--
--   Differences from the source:
--   - reading: "the graph after our shortcutting procedure" → $G_\phi$ with (S1)–(S5); reason: (S6) arcs are auxiliary and do not enter $d$, and the final application of Lemma 1.2 preserves $d$ by its item 1.
--   - generalization: $\Delta_r$ from Lemma 4.8 → any real $\Delta$, with the printed clamp; no hypothesis excluding negative cycles; reason: the argument does not use where $\Delta$ comes from; specializes to the algorithm's $\Delta$.
--   - generalization: the second equality for the algorithm's $\phi$ → for every potential; reason: it is the shift of walk weights under reweighting.
--   - encoding: distances → infima over walks in `EReal`; reason: $\pm\infty$ for unreachable pairs and negative cycles.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Claim 4.10, p.24, with Step 3 (S1)–(S5), p.23

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1
import Definitions.Def_BFAlmostLinear_shortcut

namespace BFAlmostLinear

/-- **Claim 4.10**, p.24. "Let G′ denote the graph after our shortcutting procedure. Then d_{G′}(s, t) = d_{G_ϕ}(s, t) =
d_G(s, t) + ϕ(s) − ϕ(t) for all s, t ∈ V."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Claim 4.10, p.24.

**Formalization Note.** `G′` is `shortcut (G_ϕ) Δ`, for any real `Δ` (`∆′` is the printed clamp) and any valid `ϕ` on a `G`
with (I1). The distances are infima over real walks, in `EReal`, so (S6), which is auxiliary, is not in `d`. No hypothesis says
there is no negative cycle. The final application of Lemma 1.2, p.24 is not part of `G′`; it preserves distances by that
lemma. The second equality holds for every `ϕ`. -/
theorem claim_4_10 {V E : Type} [Fintype V] [Fintype E] (G : WGraph V E) (hI1 : G.I1) :
    (∀ (ϕ : V → ℝ) (Δ : V → ℝ), G.IsValid ϕ → ∀ s t,
      ((G.reweight ϕ).shortcut Δ).dist (Sum.inl s) (Sum.inl t) = (G.reweight ϕ).dist s t) ∧
    (∀ (ϕ : V → ℝ) (s t : V),
      (G.reweight ϕ).dist s t = G.dist s t + ((ϕ s - ϕ t : ℝ) : EReal)) := by sorry

end BFAlmostLinear
