-- Prove2me | Theorems.Thm_AlmostMMS_theorem_5_2
-- name    : AlmostMMS.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:51:21.950991+00:00
-- url     : https://prove2.me/theorems/145e32e1-71f6-4a4e-9e88-4c8e450b9bc9
-- title:
--   Theorem 5.2 — the small tail case
-- statement:
--   For every fixed $\varepsilon\in(0,1)$ and integer $q\ge3$ there is $n_{\varepsilon,q}$ such that for every $n\ge n_{\varepsilon,q}$ the following holds. With $\gamma=\min(\varepsilon,1/(2q))$, $\lambda=2q/(2q-1)$ and $\rho_{q,n}$ as in Theorem 3.3, if
--   $$
--   \overline T=\frac1n\sum_{i\in N}T_i<\frac{\rho_{q,n}}{\gamma},
--   $$
--   there are $I\subseteq N$ with $|I|\ge d$ and head and tail profiles $(\pi_i,\psi_i)$, $i\in I$, with $v(\pi_i)+v(\psi_i)\ge1-2/q$ for all $i\in I$, and
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)+\sum_{i\in I}P_i(\psi_i,\ell)\le\ell\qquad\text{for every }0\le\ell\le m.
--   $$
--   Here $1\le d\le(1-\varepsilon)n$. With Lemma 2.2 this settles Theorem 3.1 when the average tail is small.
--
--   Differences from the source:
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 5.2, p.43

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_rhoQN

namespace AlmostMMS

open Finset

/-- **Theorem 5.2 (Small tail), p.43.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): for every fixed `ε ∈ (0, 1)` and integer `q ≥ 3` there is
`n_{ε,q}` such that for every `n ≥ n(ε, q)`: if `T̄ < ρ_{q,n}/γ`, there are `I ⊆ N` with `|I| ≥ d` and head and
tail profiles `(π_i, ψ_i)`, `i ∈ I`, with `v(π_i) + v(ψ_i) ≥ 1 - 2/q` and `P(Π_I, ℓ) + P(Ψ_I, ℓ) ≤ ℓ` for every
`0 ≤ ℓ ≤ m`.

**Formalization Note.** `n₀` comes before `d`, `m` and the instance; the standing `1 ≤ d ≤ (1 - ε) n` and
the ordered instance are in the binders. -/
theorem theorem_5_2 (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (q : ℕ) (hq : 3 ≤ q) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ (m d : ℕ) (J : OrderedInstance n m d), 1 ≤ d →
      (d : ℝ) ≤ (1 - ε) * (n : ℝ) → avgTail J.v q < rhoQN q d n / gammaQ ε q →
      ∃ I : Finset (Fin n), d ≤ I.card ∧ ∃ π ψ : Fin n → Multiset ℝ,
        (∀ i ∈ I, IsHeadProfile q (π i)) ∧ (∀ i ∈ I, IsTailProfile q (ψ i)) ∧
        (∀ i ∈ I, 1 - 2 / (q : ℝ) ≤ (π i).sum + (ψ i).sum) ∧
        ∀ ℓ ≤ m, ∑ i ∈ I, load J.v i (π i) ℓ + ∑ i ∈ I, load J.v i (ψ i) ℓ ≤ ℓ := by sorry

end AlmostMMS
