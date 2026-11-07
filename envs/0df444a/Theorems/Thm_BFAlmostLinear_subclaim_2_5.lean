-- Prove2me | Theorems.Thm_BFAlmostLinear_subclaim_2_5
-- name    : BFAlmostLinear.subclaim_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:56.725365+00:00
-- url     : https://prove2.me/theorems/4c941284-15f6-4f31-8756-cb7fd44a7ef6
-- title:
--   Subclaim 2.5 — at most $O((|S||T||N|)^{|S\cup T|})$ distinct sets $\mathcal X_\phi[S,*,T]$
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $V$ be a finite set, $S,T,N\subseteq V$ nonempty, and $c:V\times V\times V\to\mathbb R\cup\{+\infty\}$ any function. For a potential $\phi:V\to\mathbb R$ let
--   $$X_\phi=\{(s,r,t)\in S\times N\times T : c(s,r,t)+\phi(s)-\phi(t)<0\}.$$
--   Then, as $\phi$ ranges over all potentials, the number of distinct sets $X_\phi$ is at most
--   $$C\,(|S|\cdot|T|\cdot|N|)^{|S\cup T|}.$$
--
--   With $c(s,r,t)=d^{h}(s,r)+d^{h}(r,t)$ the set $X_\phi$ is $\mathcal X_\phi[S,*,T]$ (p.7), so this is the union-bound count behind Lemma 2.4.
--
--   **Formalization Note** The family of sets is a finite set of subsets of $S\times N\times T$, so its size cannot be a junk value.
--
--   Differences from the source:
--   - generalization: $c(s,r,t)=d^h(s,r)+d^h(r,t)$ → any $c$ that is never $-\infty$; reason: $(s,r,t)\in\mathcal X_\phi$ iff $d^h(s,r)+d^h(r,t)+\phi(s)-\phi(t)<0$ (p.7), and the hop distances are never $-\infty$ under frozen flags, so the printed claim is the special case (including any hop pair $(h_1,h_2)$).
--   - encoding: $S,T\subseteq V$ and the set $N$ → $S,T,N$ nonempty; reason: for an empty set the printed bound $O(\cdot)$ is $0$ while one set $X_\phi$ exists, so the $O$-bound is read for nonempty sets.
--   - encoding: $O(\cdot)$ → an absolute constant $C$ chosen before $V$; reason: Lean form of the $O$.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), Subclaim 2.5, p.7

import Mathlib

namespace BFAlmostLinear

open Classical in
/-- **Subclaim 2.5**, p.7. "For any S, T ⊆ V, the number of possible distinct sets X_ϕ[S, ∗, T] over all possible
potential functions ϕ is O((|S| · |T| · |N|)^{|S∪T|})."

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), Subclaim 2.5, p.7.

**Formalization Note.**
* The constant `C` is absolute: it comes before the types.
* `(s, r, t) ∈ X_ϕ` holds if and only if `c(s, r, t) + ϕ(s) − ϕ(t) < 0`, with `c(s, r, t) = d^{h₁}(s, r) + d^{h₂}(r, t)`, by
  the shift of a reweighting (p.7). The statement is for any `c` that is never `⊥`, which covers this `c`.
* `S`, `T`, `N` are nonempty: the printed bound is `0` for `N = ∅` while one set exists.
* The family is a `Finset`, a filter of a powerset, so that its cardinality cannot be a junk value. -/
theorem subclaim_2_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (S T N : Finset V) (c : V → V → V → EReal),
        S.Nonempty → T.Nonempty → N.Nonempty → (∀ s r t, c s r t ≠ ⊥) →
        ((((S ×ˢ N ×ˢ T).powerset.filter fun X =>
            ∃ ϕ : V → ℝ, ∀ x ∈ S ×ˢ N ×ˢ T,
              x ∈ X ↔ c x.1 x.2.1 x.2.2 + ((ϕ x.1 - ϕ x.2.2 : ℝ) : EReal) < 0).card : ℕ) : ℝ) ≤
          C * (((S.card * T.card * N.card : ℕ) : ℝ)) ^ (S ∪ T).card := by sorry

end BFAlmostLinear
