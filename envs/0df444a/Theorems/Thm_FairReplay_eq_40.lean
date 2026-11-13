-- Prove2me | Theorems.Thm_FairReplay_eq_40
-- name    : FairReplay.eq_40
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:38.120529+00:00
-- url     : https://prove2.me/theorems/c8c2e0ad-ca09-476a-b0cc-bd0cd743e3b9
-- title:
--   Eq. (40) — one four-way round has null-to-alternative KL $K_{\mathrm{edge}}=r\log\frac{r}{r-d}$
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$ and put $r=1-p-s$. For one four-way replay round, with states written as $(P_0(u),P_1(u),P_0(v),P_1(v))$:
--
--   1. under the null, the observation has mass $p$ on $(1,1,1,1)$, mass $s$ on $(0,1,0,1)$ and mass $r$ on $(0,0,0,0)$;
--   2. under the alternative, it has mass $p$ on $(1,1,1,1)$, mass $s$ on $(0,1,0,1)$, mass $d$ on the new state $(0,1,0,0)$ and mass $r-d$ on $(0,0,0,0)$;
--   3. the Kullback–Leibler divergence from the null law to the alternative law is
--
--   $$
--   K_{\mathrm{edge}}=r\log\frac{r}{r-d}.
--   $$
--
--   This is the per-round information that the four-way lower bound (34) divides by.
--
--   **Formalization Note** States are passed through the injective code; the divergence is Mathlib's `klDiv` in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: KL divergence of two finite laws (a real number) → Mathlib klDiv in ℝ≥0∞, compared with ENNReal.ofReal of the formula; reason: Lean convention; the formula is positive under the hypotheses, so no instance changes
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), proof of Theorem 10.4, eq. (40), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_FairReplay_fourWayModel

open MeasureTheory InformationTheory

namespace FairReplay

/-- **Eq. (40), the KL of one four-way round** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), proof of Theorem 10.4, eq. (40), p.15
(PDF p.17)): "For the lower bound, the four-output observation has the same mass p on the all-one
state and the same mass s on the state in which both new-version outputs are one while both
old-version outputs are zero. Under the null, the remaining all-zero state has mass r = 1 − p − s.
Under the alternative, mass d is split from that state into a new state witnessing the
counterfactual differential. Hence the null-to-alternative KL of one four-way round is
K_edge = r log(r/(r − d))."

With `r = 1 − p − s`, the null law of the coded four-way observation puts masses `p, s, r` on
`(1,1,1,1)`, `(0,1,0,1)`, `(0,0,0,0)`; the alternative law puts `p, s, d, r − d` on `(1,1,1,1)`,
`(0,1,0,1)`, `(0,1,0,0)`, `(0,0,0,0)`; and the KL divergence from the null to the alternative is
`r log(r/(r − d))`.

**Formalization Note** States are ordered `(P0(u), P1(u), P0(v), P1(v))` and passed through the
injective code `obsCode`. The KL divergence is Mathlib's `klDiv` in `ℝ≥0∞`. -/
theorem eq_40 (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p + s + d < 1) :
    let r := 1 - p - s
    let μ₀ := (fourWayModel p s d false).P 0
    let μ₁ := (fourWayModel p s d true).P 0
    μ₀ {obsCode (![true, true, true, true] : Fin 4 → Bool)} = ENNReal.ofReal p ∧
      μ₀ {obsCode (![false, true, false, true] : Fin 4 → Bool)} = ENNReal.ofReal s ∧
      μ₀ {obsCode (![false, false, false, false] : Fin 4 → Bool)} = ENNReal.ofReal r ∧
      μ₁ {obsCode (![true, true, true, true] : Fin 4 → Bool)} = ENNReal.ofReal p ∧
      μ₁ {obsCode (![false, true, false, true] : Fin 4 → Bool)} = ENNReal.ofReal s ∧
      μ₁ {obsCode (![false, true, false, false] : Fin 4 → Bool)} = ENNReal.ofReal d ∧
      μ₁ {obsCode (![false, false, false, false] : Fin 4 → Bool)} = ENNReal.ofReal (r - d) ∧
      klDiv μ₀ μ₁ = ENNReal.ofReal (r * Real.log (r / (r - d))) := by sorry

end FairReplay
