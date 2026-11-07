-- Prove2me | Theorems.Thm_AlmostMMS_theorem_3_3
-- name    : AlmostMMS.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:55.199027+00:00
-- url     : https://prove2.me/theorems/7020800e-8324-469e-855c-8046a556d037
-- title:
--   Theorem 3.3 — the large tail case
-- statement:
--   Let $\gamma=\min(\varepsilon,1/(2q))$ and $\lambda=2q/(2q-1)$. Suppose
--   $$
--   \overline T=\frac1n\sum_{i\in N}T_i\ge\frac{\rho_{q,n}}{\gamma},\qquad\rho_{q,n}=8+4\log_\lambda\big(q^3d^2(d+2)n\big)+8q\log\big((d+2)n\big).
--   $$
--   Then there are $I\subseteq N$ with $|I|\ge d$ and head profiles $\pi_i$, $i\in I$, such that $T_i=0$ implies $\Delta(\pi_i)=0$, and for every $0\le\ell\le m$,
--   $$
--   \sum_{i\in I}P_i(\pi_i,\ell)\le\ell-\sum_{i\in I}\tau_i(\pi_i)(\ell-h_i)_+.
--   $$
--   Here $\varepsilon\in(0,1)$, $q\ge3$ and $1\le d\le(1-\varepsilon)n$ are §3's standing assumptions. With Lemma 3.1 and Lemma 2.2 this settles Theorem 3.1 when the average tail is large.
--
--   Differences from the source:
--   - encoding: §§3–5's standing ordered instance with MMS bundles of value 1 → a structure `J : OrderedInstance n m d`; reason: the structure holds exactly Assumption 1's three bullets
--   - encoding: a family {π_i}_{i∈I} → a total function on agents read only on I; reason: values off I play no role
--   - encoding: (ℓ − h_i)₊ → truncated natural subtraction cast to ℝ; reason: the two agree on ℕ
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 3.3, pp.25–26

import Mathlib
import Definitions.Def_AlmostMMS_OrderedInstance
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_Q
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit
import Definitions.Def_AlmostMMS_rhoQN

namespace AlmostMMS

open Finset

/-- **Theorem 3.3 (Large tail), pp.25–26.** Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): let `γ = min(ε, 1/(2q))` and `λ = 2q/(2q-1)`. If
`T̄ ≥ ρ_{q,n}/γ`, with `ρ_{q,n} = 8 + 4 log_λ(q³d²(d+2)n) + 8q log((d+2)n)`, there are `I ⊆ N` with `|I| ≥ d`
and head profiles `π_i`, `i ∈ I`, such that `T_i = 0` implies `Δ(π_i) = 0`, and for every `0 ≤ ℓ ≤ m`,
`P(Π_I, ℓ) ≤ ℓ - ∑_{i ∈ I} τ_i(π_i) (ℓ - h_i)₊`.

**Formalization Note.** The binders carry §3's standing assumptions: `ε ∈ (0, 1)`, `q ≥ 3`,
`1 ≤ d ≤ (1 - ε) n` and an ordered instance. There is no threshold on `n`. -/
theorem theorem_3_3 {n m d q : ℕ} (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hq : 3 ≤ q) (hd : 1 ≤ d)
    (hdn : (d : ℝ) ≤ (1 - ε) * (n : ℝ)) (J : OrderedInstance n m d)
    (hT : rhoQN q d n / gammaQ ε q ≤ avgTail J.v q) :
    ∃ I : Finset (Fin n), d ≤ I.card ∧ ∃ π : Fin n → Multiset ℝ,
      (∀ i ∈ I, IsHeadProfile q (π i)) ∧
      (∀ i ∈ I, tailVal J.v q i = 0 → deficit q (π i) = 0) ∧
      ∀ ℓ ≤ m, ((∑ i ∈ I, load J.v i (π i) ℓ : ℕ) : ℝ) ≤ (ℓ : ℝ) -
        ∑ i ∈ I, tauOf J.v q i (some (π i)) * ((ℓ - headCount J.v q i : ℕ) : ℝ) := by sorry

end AlmostMMS
