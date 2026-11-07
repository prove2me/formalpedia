-- Prove2me | Theorems.Thm_BFAlmostLinear_lemma_4_16
-- name    : BFAlmostLinear.lemma_4_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:41:18.566867+00:00
-- url     : https://prove2.me/theorems/d612deb0-ba85-4d11-aeab-738127e3ca47
-- title:
--   Lemma 4.16 (Unfolding Lemma) — unfolding the last (first) arc into lower levels with $t$ extra hops
-- statement:
--   Let $G$ be a weighted graph with frozen flags and a level function $i:V\to\{0,\dots,t\}$ satisfying (I2), (I4) and the path part of (I3). Walks below use real arcs and flagged auxiliary arcs.
--
--   1. If $P$ is a nonempty walk from a negative vertex $r$ to $u$ with at most $h$ hops, there is a nonempty walk $P'$ from $r$ to $u$ with at most $h+t$ hops and the same weight whose last arc $(w',u)$ satisfies $i(w')<i(u)$ if $i(u)>0$, and $i(w')=0$ if $i(u)=0$.
--   2. If $P$ is a nonempty walk from $u$ to a negative vertex $r$ with at most $h$ hops, there is a nonempty walk $P'$ from $u$ to $r$ with at most $h+t$ hops and the same weight whose first arc $(u,w')$ satisfies $i(w')<i(u)$ if $i(u)>0$, and $i(w')=0$ if $i(u)=0$.
--
--   This is the second of the paper's new tools: arcs at Steiner vertices can be charged to arcs between original vertices.
--
--   Differences from the source:
--   - generalization: $G(t)$, the graph after $t$ iterations → any graph with a level function bounded by $t$ satisfying (I2), (I4) and the path part of (I3); reason: these are the properties of $G(t)$ the proof uses; reweighting preserves the path part of (I3) (p.11).
--   - reading: "path in $G(t)$" → walk of real arcs and flagged auxiliary arcs; reason: unflagged auxiliary arcs such as (S6) fall outside (I3) and cannot be unfolded; walks as in §1.1.
--   - encoding: "let $(w,u)$ be the last edge in $P$" → $P$ nonempty; reason: the last edge must exist.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Lemma 4.16, p.28; G(t) and i(u), p.12

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph_I1

namespace BFAlmostLinear

/-- **Lemma 4.16 (Unfolding Lemma)**, p.28. "• Suppose that there is an h-hop path P in G(t) from r ∈ N to u and let (w, u) be the
last edge in P. Then there exists an (h + t)-hop path P′ in G(t) from r to u of the same weight as P such that the final edge
(w′, u) in P′ satisfies i(w′) < i(u) if i(u) > 0 and i(w′) = 0 if i(u) = 0. • Suppose that there is an h-hop path P in G(t) from u to
r ∈ N and let (u, w) be the first edge in P. Then there exists an (h + t)-hop path P′ in G(t) from u to r of the same weight as P
such that the first edge (u, w′) in P′ satisfies i(w′) < i(u) if i(u) > 0 and i(w′) = 0 if i(u) = 0."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Lemma 4.16, p.28.

**Formalization Note.** The statement is free of the run: any graph with a level function `i` with values at most `t`, (I2), (I4) and
the weight-and-path part of (I3), which is the part preserved by reweighting, so it holds in `G(t)` (p.12: "after applying the
reweighting but before applying the data structure"). `P` is nonempty. `P` and `P′` use real arcs and flagged auxiliary arcs
(`Usable`); with no auxiliary arcs this is every arc. An unflagged auxiliary arc such as (S6) falls outside (I3), so it cannot be
unfolded and is excluded. -/
theorem lemma_4_16 {V E : Type} (G : WGraph V E) (level : V → ℕ) (t : ℕ)
    (hlev : ∀ v, level v ≤ t) (hI2 : G.I2 level) (hI3 : G.I3Path level) (hI4 : G.I4 level) :
    (∀ (r u : V) (h : ℕ) (P₀ : List E) (e : E), G.IsNegVertex r →
      G.net.IsPathFrom r u (P₀ ++ [e]) → (∀ x ∈ P₀ ++ [e], G.Usable x) → G.hops (P₀ ++ [e]) ≤ h →
      ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom r u (P₁ ++ [e']) ∧
        (∀ x ∈ P₁ ++ [e'], G.Usable x) ∧ G.hops (P₁ ++ [e']) ≤ h + t ∧
        pathWeight G.w (P₁ ++ [e']) = pathWeight G.w (P₀ ++ [e]) ∧
        (0 < level u → level (G.net.tail e') < level u) ∧
        (level u = 0 → level (G.net.tail e') = 0)) ∧
    (∀ (r u : V) (h : ℕ) (P₀ : List E) (e : E), G.IsNegVertex r →
      G.net.IsPathFrom u r (e :: P₀) → (∀ x ∈ e :: P₀, G.Usable x) → G.hops (e :: P₀) ≤ h →
      ∃ (P₁ : List E) (e' : E), G.net.IsPathFrom u r (e' :: P₁) ∧
        (∀ x ∈ e' :: P₁, G.Usable x) ∧ G.hops (e' :: P₁) ≤ h + t ∧
        pathWeight G.w (e' :: P₁) = pathWeight G.w (e :: P₀) ∧
        (0 < level u → level (G.net.head e') < level u) ∧
        (level u = 0 → level (G.net.head e') = 0)) := by sorry

end BFAlmostLinear
