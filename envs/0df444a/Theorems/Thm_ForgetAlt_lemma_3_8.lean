-- Prove2me | Theorems.Thm_ForgetAlt_lemma_3_8
-- name    : ForgetAlt.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:23:10.320322+00:00
-- url     : https://prove2.me/theorems/5a1e919c-0e65-4a71-a89b-62c1bdf7183d
-- title:
--   Lemma 3.8: $\mathrm{vlevel}(v)=\min_{e\in\tilde E_T(v)}\mathrm{vlevel}(e)$; free vertices have volume $\ge 2\ell+5$
-- statement:
--   Let $T$ be any ABT. For every vertex $v$ of $T$,
--
--   $$\mathrm{vlevel}(v)=\min_{e\in\tilde E_T(v)}\mathrm{vlevel}(e),$$
--
--   where the minimum of an empty set is $\infty$. If $v$ is a free vertex, then $\mathrm{vlevel}(v)\ge2\ell+5$, with equality if and only if $v$ is an endpoint of a shortest augmenting path.
--
--   Differences from the source:
--   - encoding: graphs are finite (standing convention of the paper) → a finite vertex type, [Finite V]; reason: Lean convention; every graph of the paper is finite
--   - encoding: ℓ, with 2ℓ + 1 the length of a shortest augmenting path (|U| ≥ 2 assumed throughout) → hypothesis HasAugPath M; reason: ℓ is undefined when (G, M) has no augmenting path; the hypothesis only excludes that case
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.8, printed p.22 (PDF p.23)

import Mathlib
import Definitions.Def_ForgetAlt_ABT

namespace ForgetAlt

open BergeMatching.Core

/-- **Lemma 3.8**, printed p.22 (PDF p.23). Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…).

"Let `T` be any ABT. For any vertex `v ∈ V(T)`, `vlevel(v) = min_{e ∈ Ẽ_T(v)} vlevel(e)` holds,
where the minimum of an empty set is `∞`. If `v` is a free vertex, then `vlevel(v) ≥ 2ℓ + 5`,
where the equality holds if and only if `v` is an endpoint of a shortest augmenting path."

**Formalization Note.** The minimum is an infimum in `ℕ∞` (`⊤` over the empty set). The second
sentence assumes an augmenting path exists, so that `ℓ` is defined. -/
theorem lemma_3_8 {V : Type} [Finite V] (G : SimpleGraph V) (M : G.Subgraph) (hM : M.IsMatching)
    (par : ExtV V → ExtV V) (hT : IsABT G M par) :
    (∀ v, Reach G M v → vlevelV G M v = ⨅ (e : Sym2 (ExtV V)) (_ : IsIncoming G M par v e), vlevelE G M e) ∧
    (HasAugPath M → ∀ u : V, IsNeutral M u →
      ((2 * ell M + 5 : ℕ) : ℕ∞) ≤ vlevelV G M (.orig u) ∧
      (vlevelV G M (.orig u) = ((2 * ell M + 5 : ℕ) : ℕ∞) ↔
        ∃ (a b : V) (p : G.Walk a b), IsShortestAugPath M p ∧ (a = u ∨ b = u))) := by sorry

end ForgetAlt
