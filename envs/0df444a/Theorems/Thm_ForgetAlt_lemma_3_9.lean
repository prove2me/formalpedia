-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_9
-- name    : ForgetAlt.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:25:00.466237+00:00
-- url     : https://prove2.me/theorems/a8e2d4b2-9bb1-4faa-8ce5-16d1cd46d467
-- title:
--   Lemma 3.9: localized reconstruction of a shortest augmenting path in $O(|X|+1)$ time
-- statement:
--   Let $T$ be any ABT with fixed MIEs, and let $e=\{y,z\}$ be a critical edge of volume $2\ell+5$ with $y\in V(T(u))$ and $z\in V(T(t))$ for two distinct free vertices $u,t$. Then $\textsc{PathConstruction}(T,u,t,\mathrm{odd},e)$ outputs a shortest augmenting path
--
--   $$X=X[u,y]\circ e\circ X[z,t]$$
--
--   from $u$ to $t$ in $O(|X|+1)$ time, where $X[u,y]$ lies in $T(u)$, $X[z,t]$ lies in $T(t)$, and every non-tree edge of $X$ other than $e$ has volume less than $2\ell+5$.
--
--   Differences from the source:
--   - encoding: an arbitrary finite graph G → a graph on the vertex set Fin n; reason: every finite graph is isomorphic to one on Fin n; the machine part needs numbered vertices
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
--   - reading: outputs … in O(|X| + 1) time → there is one program of the published word RAM EndStatement (constants b, C) whose step count on the stated input layout is at most C·(bound + 1), at every word width W ≥ b·(⌊log₂ size⌋ + 1); reason: the paper's time bounds are word-RAM bounds with O(log n)-bit words; the + 1 only matters when the bound is 0
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.9, printed pp.22–23 (PDF pp.23–24)

import Mathlib
import Definitions.Def_ForgetAlt_Layouts

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.9** (Localized path reconstruction), printed pp.22–23 (PDF pp.23–24). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `T` be any ABT, and let `e = {y, z}` be a critical edge of volume `2ℓ + 5` such that
`y ∈ V(T(u))` and `z ∈ V(T(t))` for two distinct free vertices `u` and `t`. Then
`PathConstruction(T, u, t, odd, e)` outputs a shortest augmenting path
`X = X[u, y] ∘ e ∘ X[z, t]` from `u` to `t` in `O(|X| + 1)` time, where `X[u, y]` and `X[z, t]`
lie in `T(u)` and `T(t)`, respectively, and every non-tree edge of `X` other than `e` has volume
less than `2ℓ + 5`."

**Formalization Note.** Vertex set `Fin n`; `T` any ABT, `e*_T` any MIE choice (the procedure
uses them). `X` is a walk of `G`; its vertex list splits as `X₁ ++ X₂` with `X₁` ending at `y`
and `X₂` starting at `z`, so `e` joins them. One word-RAM program for all inputs, run on the
`pcInput` layout, halts within `C·(|X| + 1)` steps with `X` as output. -/
theorem lemma_3_9 :
    ∃ (prog : List EndStatement.Instr) (b C : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (M : G.Subgraph), M.IsMatching → HasAugPath M →
      ∀ par : ExtV (Fin n) → ExtV (Fin n), IsABT G M par →
      ∀ mie : ExtV (Fin n) → Sym2 (ExtV (Fin n)), MIEChoice G M par mie →
      ∀ y z u t : Fin n, IsCritical G M s(.orig y, .orig z) →
        vlevelE G M s(.orig y, .orig z) = ((2 * ell M + 5 : ℕ) : ℕ∞) →
        IsNeutral M u → IsNeutral M t → u ≠ t →
        InSubtree G M par (.orig u) (.orig y) → InSubtree G M par (.orig t) (.orig z) →
        ∃ (X : G.Walk u t) (X₁ X₂ : List (Fin n)),
          PCReturns G M par mie (.orig u) (.orig t) .odd s(.orig y, .orig z)
            (X.support.map .orig) ∧
          IsShortestAugPath M X ∧ X.support = X₁ ++ X₂ ∧ X₁.getLast? = some y ∧
          X₂.head? = some z ∧ (∀ w ∈ X₁, InSubtree G M par (.orig u) (.orig w)) ∧
          (∀ w ∈ X₂, InSubtree G M par (.orig t) (.orig w)) ∧
          (∀ e ∈ X.edges, e ≠ s(y, z) → ¬ IsTreeEdge G M par (e.map .orig) →
            vlevelE G M (e.map .orig) < ((2 * ell M + 5 : ℕ) : ℕ∞)) ∧
          ∀ W : ℕ, b * (Nat.log2 (n + 2) + 1) ≤ W →
            ∃ t' ≤ C * (X.length + 1),
              RunOutputs prog W t' n (pcInput G M par mie (.orig u) (.orig t) .odd s(.orig y, .orig z))
                (fun out => Decodes out (encExtPath (X.support.map .orig))) := by sorry

end ForgetAlt
