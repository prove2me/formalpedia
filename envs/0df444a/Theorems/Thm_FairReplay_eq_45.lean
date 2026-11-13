-- Prove2me | Theorems.Thm_FairReplay_eq_45
-- name    : FairReplay.eq_45
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:46:26.574291+00:00
-- url     : https://prove2.me/theorems/50d5dfe9-355e-4773-b361-045099edd2fb
-- title:
--   Eq. (45) — $K_{\mathrm{edge}}=d+O(d^2)$
-- statement:
--   Fix $p,s>0$ with $p+s<1$ and put $r=1-p-s$. As $d\to0$,
--
--   $$
--   K_{\mathrm{edge}}=r\log\frac{r}{r-d}=d+O(d^2):
--   $$
--
--   there are constants $C,d_0>0$ (depending on $p,s$) such that $\bigl|r\log\frac{r}{r-d}-d\bigr|\le C\,d^2$ for every $d\in(0,d_0)$.
--
--   Together with (34) this gives the four-way lower bound of order $\log(1/\delta)/d$.
--
--   Differences from the source:
--   - encoding: K_edge = d + O(d²) as d → 0 → ∃ C d₀ > 0, ∀ d ∈ (0, d₀), |r log(r/(r − d)) − d| ≤ C d²; reason: the definition of O(·) at 0⁺ with r fixed
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), proof of Theorem 10.4, eq. (45), p.15 (PDF p.17)

import Mathlib

namespace FairReplay

/-- **Eq. (45), K_edge = d + O(d²)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), proof of Theorem 10.4, eq. (45), p.15 (PDF p.17)):
"Finally, K_edge = d + O(d²), (45)" where K_edge = r log(r/(r − d)) (40) and r = 1 − p − s.

For fixed `p, s > 0` with `p + s < 1` and `r = 1 − p − s`, there are constants `C, d₀ > 0` with
`|r log(r/(r − d)) − d| ≤ C d²` for every `d ∈ (0, d₀)`.

**Formalization Note** The `O(d²)` as `d → 0` is written out with explicit constants chosen before
`d` (they depend only on `p, s`). -/
theorem eq_45 (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hps : p + s < 1) :
    ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      |(1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)) - d| ≤ C * d ^ 2 := by sorry

end FairReplay
