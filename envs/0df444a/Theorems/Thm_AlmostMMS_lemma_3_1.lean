-- Prove2me | Theorems.Thm_AlmostMMS_lemma_3_1
-- name    : AlmostMMS.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:44.722543+00:00
-- url     : https://prove2.me/theorems/1e68e6dc-2fee-4fd9-9192-e2bbf2c3e866
-- title:
--   Lemma 3.1 — tail completion
-- statement:
--   Let $I\subseteq N$, let $\pi_i$ be a head profile of $i\in I$, and assume that $T_i=0$ implies $\Delta(\pi_i)=0$. If for every $0\le\ell\le m$
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)\le\ell-\sum_{i\in I}\tau_i(\pi_i)(\ell-h_i)_+,
--   $$
--   there are tail profiles $\psi_i$, $i\in I$, with
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)+\sum_{i\in I}P_i(\psi_i,\ell)\le\ell\quad(0\le\ell\le m),\qquad v(\pi_i)+v(\psi_i)\ge1-\frac2q\quad(i\in I).
--   $$
--   The slack in the hypothesis pays for the tail demands. Without the condition on $T_i=0$ the claim fails, since then $\tau_i=0$ for a profile with positive deficit.
--
--   Differences from the source:
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
--   - encoding: (ℓ − h_i)₊ → truncated natural subtraction cast to ℝ; reason: the two agree on ℕ
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Lemma 3.1, p.21

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit

namespace AlmostMMS

open Finset

/-- **Lemma 3.1 (Tail completion), p.21.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `π_i` be a head profile of `i ∈ I`, and assume
`T_i = 0` implies `Δ(π_i) = 0`. If `P(Π_I, ℓ) ≤ ℓ - ∑_{i ∈ I} τ_i(π_i)(ℓ - h_i)₊` for every `0 ≤ ℓ ≤ m`,
there are tail profiles `ψ_i` with `P(Π_I, ℓ) + P(Ψ_I, ℓ) ≤ ℓ` for every `0 ≤ ℓ ≤ m` and
`v(π_i) + v(ψ_i) ≥ 1 - 2/q` for `i ∈ I`.

**Formalization Note.** `IsTailProfile` requires positive demands (Definition 3.2). The printed
construction can add a demand of value `0`; dropping it keeps the value and lowers the loads. A profile
`π_i` of `i ∉ I` plays no role. -/
theorem lemma_3_1 {n m d q : ℕ} (hq : 3 ≤ q) (J : OrderedInstance n m d) (I : Finset (Fin n))
    (π : Fin n → Multiset ℝ) (hπ : ∀ i ∈ I, IsHeadProfile q (π i))
    (hT : ∀ i ∈ I, tailVal J.v q i = 0 → deficit q (π i) = 0)
    (hload : ∀ ℓ ≤ m, ((∑ i ∈ I, load J.v i (π i) ℓ : ℕ) : ℝ) ≤ (ℓ : ℝ) -
      ∑ i ∈ I, tauOf J.v q i (some (π i)) * ((ℓ - headCount J.v q i : ℕ) : ℝ)) :
    ∃ ψ : Fin n → Multiset ℝ, (∀ i ∈ I, IsTailProfile q (ψ i)) ∧
      (∀ ℓ ≤ m, ∑ i ∈ I, load J.v i (π i) ℓ + ∑ i ∈ I, load J.v i (ψ i) ℓ ≤ ℓ) ∧
      ∀ i ∈ I, 1 - 2 / (q : ℝ) ≤ (π i).sum + (ψ i).sum := by sorry

end AlmostMMS
