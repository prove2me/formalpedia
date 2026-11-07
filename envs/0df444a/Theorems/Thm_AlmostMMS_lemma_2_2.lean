-- Prove2me | Theorems.Thm_AlmostMMS_lemma_2_2
-- name    : AlmostMMS.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:29.011362+00:00
-- url     : https://prove2.me/theorems/86444891-0e3a-43d8-96ab-1ce5b719e6ff
-- title:
--   Lemma 2.2 — simultaneous satisfaction iff prefix loads fit
-- statement:
--   Let $I\subseteq N$, let $\pi_i$ be a demand profile of agent $i\in I$, and let $F\subseteq M$. The profiles can be simultaneously satisfied using distinct items of $F$ if and only if
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)\le|F\cap[\ell]|\qquad\text{for all }0\le\ell\le m.
--   $$
--   Furthermore, with $K=\sum_{i\in I}|\pi_i|$, the first $K$ items of $F$ suffice; and when $F=M$, the items $\{1,\dots,K\}$ suffice as long as the load at each prefix $\ell$ is at most $\ell$. This turns finding an allocation into finding profiles with bounded prefix loads.
--
--   Differences from the source:
--   - generalization: demands in (0, 1], and §2's setting → any real demands, and any values non-increasing along the item order; reason: the argument uses the order only; the source's demands are a special case
--   - reading: K := ∑_{i∈π_i} |π_i| → K := ∑_{i∈I} |π_i|; reason: a typo; the proof on p.13 has ∑_{i∈I}
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 2.2, p.12

import Mathlib
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_SimulSatisfied

namespace AlmostMMS

open Finset

/-- **Lemma 2.2, p.12.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): the profiles `π_i`, `i ∈ I`, can be simultaneously satisfied using
distinct items of `F` if and only if `P(Π_I, ℓ) ≤ |F ∩ [ℓ]|` for all `0 ≤ ℓ ≤ m`. Furthermore, with
`K = ∑_{i ∈ I} |π_i|`, the first `K` items of `F` suffice, and when `F = M` the items `{1, …, K}` suffice
as long as `P(Π_I, ℓ) ≤ ℓ` for all `0 ≤ ℓ ≤ m`.

**Formalization Note.** The printed `∑_{i ∈ π_i}` is a typo for `∑_{i ∈ I}`. Only the common item order
(`Antitone (v i)`) is assumed; demands may be arbitrary reals. -/
theorem lemma_2_2 {n m : ℕ} (v : Fin n → Fin m → ℝ) (hv : ∀ i, Antitone (v i))
    (I : Finset (Fin n)) (π : Fin n → Multiset ℝ) (F : Finset (Fin m)) :
    (SimulSatisfied v I π F ↔ ∀ ℓ ≤ m, ∑ i ∈ I, load v i (π i) ℓ ≤ prefixCount F ℓ) ∧
    ((∀ ℓ ≤ m, ∑ i ∈ I, load v i (π i) ℓ ≤ prefixCount F ℓ) →
      SimulSatisfied v I π (firstItems F (∑ i ∈ I, (π i).card))) ∧
    ((∀ ℓ ≤ m, ∑ i ∈ I, load v i (π i) ℓ ≤ ℓ) →
      SimulSatisfied v I π (univ.filter fun e => e.val < ∑ i ∈ I, (π i).card)) := by sorry

end AlmostMMS
