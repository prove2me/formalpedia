-- Prove2me | Theorems.Thm_AlmostMMS_lemma_5_2
-- name    : AlmostMMS.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:50:59.813731+00:00
-- url     : https://prove2.me/theorems/2586bb00-1b78-4f98-b9b0-a82de0c98878
-- title:
--   Lemma 5.2 — tail completion for a common tail
-- statement:
--   Let $I\subseteq N$ and let $\pi_i$ be a head profile of $i\in I$. Suppose there are an integer $0\le h^*\le m$ and a value $T^*\ge0$ such that
--
--   1. all demands of the $\pi_i$ can be simultaneously satisfied by distinct items in $\{1,\dots,h^*\}$;
--   2. $h_i/q+T_i\ge h^*/q+T^*$ for every $i\in I$ with $\Delta(\pi_i)>0$;
--   3. $\sum_{i\in I}\Delta(\pi_i)\le T^*$.
--
--   Then there are tail profiles $\psi_i$, $i\in I$, with
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)+\sum_{i\in I}P_i(\psi_i,\ell)\le\ell\quad(0\le\ell\le m),\qquad v(\pi_i)+v(\psi_i)\ge1-\frac2q\quad(i\in I).
--   $$
--   This completes the tails in the small tail case, where the agents share the tail $\{h^*+1,\dots,m\}$.
--
--   Differences from the source:
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 5.2, pp.41–42

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit
import Definitions.Def_AlmostMMS_SimulSatisfied

namespace AlmostMMS

open Finset

/-- **Lemma 5.2 (Lemma 3.1 for a common tail), pp.41–42.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `π_i` be a head profile of `i ∈ I`.
If there are an integer `0 ≤ h* ≤ m` and a value `T* ≥ 0` such that (1) all demands of `Π_I` are
simultaneously satisfied by distinct items of `{1, …, h*}`, (2) `h_i/q + T_i ≥ h*/q + T*` for every `i ∈ I`
with `Δ(π_i) > 0`, and (3) `∑_{i ∈ I} Δ(π_i) ≤ T*`, then there are tail profiles `ψ_i` with
`P(Π_I, ℓ) + P(Ψ_I, ℓ) ≤ ℓ` for all `0 ≤ ℓ ≤ m` and `v(π_i) + v(ψ_i) ≥ 1 - 2/q` for `i ∈ I`.

**Formalization Note.** As in Lemma 3.1, tail demands are positive, and a zero demand of the printed
construction is dropped. -/
theorem lemma_5_2 {n m d q : ℕ} (hq : 3 ≤ q) (J : OrderedInstance n m d) (I : Finset (Fin n))
    (π : Fin n → Multiset ℝ) (hπ : ∀ i ∈ I, IsHeadProfile q (π i)) (hs : ℕ) (hhs : hs ≤ m)
    (Ts : ℝ) (hTs : 0 ≤ Ts)
    (h1 : SimulSatisfied J.v I π (univ.filter fun e => e.val < hs))
    (h2 : ∀ i ∈ I, 0 < deficit q (π i) →
      (hs : ℝ) / (q : ℝ) + Ts ≤ (headCount J.v q i : ℝ) / (q : ℝ) + tailVal J.v q i)
    (h3 : ∑ i ∈ I, deficit q (π i) ≤ Ts) :
    ∃ ψ : Fin n → Multiset ℝ, (∀ i ∈ I, IsTailProfile q (ψ i)) ∧
      (∀ ℓ ≤ m, ∑ i ∈ I, load J.v i (π i) ℓ + ∑ i ∈ I, load J.v i (ψ i) ℓ ≤ ℓ) ∧
      ∀ i ∈ I, 1 - 2 / (q : ℝ) ≤ (π i).sum + (ψ i).sum := by sorry

end AlmostMMS
