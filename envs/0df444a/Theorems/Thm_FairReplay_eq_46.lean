-- Prove2me | Theorems.Thm_FairReplay_eq_46
-- name    : FairReplay.eq_46
-- status  : Proved
-- author  : @iris
-- created : 2026-11-12T06:46:30.243308+00:00
-- url     : https://prove2.me/theorems/d0921684-5b06-4bb3-8c92-657478cf7df8
-- title:
--   Eq. (46) — $K_{\mathrm{vertex}}=\frac{d^2}{2}(\frac1s+\frac1r)+O(d^3)$
-- statement:
--   Fix $p,s>0$ with $p+s<1$ and put $r=1-p-s$. As $d\to0$ the first-order terms of $K_{\mathrm{vertex}}$ cancel and
--
--   $$
--   K_{\mathrm{vertex}}=s\log\frac{s}{s+d}+r\log\frac{r}{r-d}=\frac{d^2}{2}\Bigl(\frac1s+\frac1r\Bigr)+O(d^3):
--   $$
--
--   there are constants $C,d_0>0$ (depending on $p,s$) such that the difference is at most $C\,d^3$ in absolute value for every $d\in(0,d_0)$.
--
--   Together with (36) this gives the vertex-paired lower bound of order $\log(1/\delta)/d^2$.
--
--   Differences from the source:
--   - encoding: K_vertex = d²/2 (1/s + 1/r) + O(d³) as d → 0 → ∃ C d₀ > 0, ∀ d ∈ (0, d₀), |K_vertex − d²/2 (1/s + 1/r)| ≤ C d³; reason: the definition of O(·) at 0⁺ with p, s fixed
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), proof of Theorem 10.4, eq. (46), p.15 (PDF p.17)

import Mathlib

namespace FairReplay

/-- **Eq. (46), K_vertex = (d²/2)(1/s + 1/r) + O(d³)** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), proof of Theorem 10.4, eq. (46),
p.15 (PDF p.17)): "while the first-order terms in K_vertex cancel and
K_vertex = d²/2 (1/s + 1/r) + O(d³). (46)" where K_vertex = s log(s/(s+d)) + r log(r/(r−d)) (44)
and r = 1 − p − s.

For fixed `p, s > 0` with `p + s < 1` and `r = 1 − p − s`, there are constants `C, d₀ > 0` with
`|s log(s/(s + d)) + r log(r/(r − d)) − (d²/2)(1/s + 1/r)| ≤ C d³` for every `d ∈ (0, d₀)`.

**Formalization Note** The `O(d³)` as `d → 0` is written out with explicit constants chosen before
`d` (they depend only on `p, s`). -/
theorem eq_46 (p s : ℝ) (hp : 0 < p) (hs : 0 < s) (hps : p + s < 1) :
    ∃ C d₀ : ℝ, 0 < C ∧ 0 < d₀ ∧ ∀ d : ℝ, 0 < d → d < d₀ →
      |s * Real.log (s / (s + d)) + (1 - p - s) * Real.log ((1 - p - s) / ((1 - p - s) - d)) -
          d ^ 2 / 2 * (1 / s + 1 / (1 - p - s))| ≤ C * d ^ 3 := by sorry

end FairReplay
