-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_harmonic_Hm
-- name    : CorrelatedLocalSearch.harmonic_Hm
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:39:06.109666+00:00
-- url     : https://prove2.me/theorems/09be0f5f-e12e-48aa-9b0b-7a48f5ce9079
-- title:
--   Proof of Lemma C.1 — $H_m$ is increasing, $H_m(0)=0$, $H_m(m)=1$, and harmonic
-- statement:
--   Let $k/2<r<k$, $m\ge1$, and $H_m(d)=\frac dm\lambda^{d-m}$. Then
--
--   1. $H_m$ is strictly increasing on $\{0,1,\dots,m\}$;
--   2. $H_m(0)=0$ and $H_m(m)=1$;
--   3. for $1\le d<m$,
--   $$
--   a\,H_m(d-1)+b\,H_m(d+1)=H_m(d),\qquad a=r\,k^{-s_*},\ b=(k-r)\,k^{-s_*}.
--   $$
--
--   Together with (21) these properties bound the weight of prefixes that first reach the barrier $m$ by $H_m(h)$.
--
--   Differences from the source:
--   - encoding: integers k/2 < r < k → natural numbers k, r with k < 2r and r < k; reason: same instances
--   - reading: H_m is increasing → H_m is strictly increasing on {0, …, m}; reason: the stronger reading; d λ^d is strictly increasing for λ > 1
--   - generalization: a barrier m > h ≥ 1 (so m ≥ 2) → 1 ≤ m; reason: the case m = 1 is added (H_1(0) = 0, H_1(1) = 1, no harmonic clause) and every barrier m ≥ 2 of the paper is an instance; H_m(m) = 1 fails at m = 0
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar
import Definitions.Def_CorrelatedLocalSearch_Hm

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The harmonic function `H_m` (Xu, *Local Search with Correlated Randomness*,
arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22):
`H_m(d) = (d/m) λ^{d−m}` is increasing on `0 ≤ d ≤ m`, `H_m(0) = 0`, `H_m(m) = 1`, and
`a H_m(d − 1) + b H_m(d + 1) = H_m(d)` for `1 ≤ d < m`, with `a = r k^{−s∗}`,
`b = (k − r) k^{−s∗}`.

**Formalization Note** "Increasing" is stated as strict monotonicity on `{0, …, m}`. The barrier
satisfies `m > h ≥ 1` in the paper; `1 ≤ m` is assumed (for `m = 0`, `H_0 ≡ 0` and
`H_m(m) = 1` fails). -/
theorem harmonic_Hm (k r : ℕ) (hk : k < 2 * r) (hr : r < k) (m : ℕ) (hm : 1 ≤ m) :
    (∀ d₁ d₂ : ℕ, d₁ < d₂ → d₂ ≤ m → Hm k r m d₁ < Hm k r m d₂) ∧
      Hm k r m 0 = 0 ∧ Hm k r m m = 1 ∧
      ∀ d : ℕ, 1 ≤ d → d < m →
        (r : ℝ) * (k : ℝ) ^ (-sStar k r) * Hm k r m (d - 1) +
            ((k : ℝ) - r) * (k : ℝ) ^ (-sStar k r) * Hm k r m (d + 1) = Hm k r m d := by sorry

end CorrelatedLocalSearch
