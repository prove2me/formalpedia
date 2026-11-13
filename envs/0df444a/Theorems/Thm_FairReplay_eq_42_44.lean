-- Prove2me | Theorems.Thm_FairReplay_eq_42_44
-- name    : FairReplay.eq_42_44
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:49:32.17675+00:00
-- url     : https://prove2.me/theorems/88f0dd8c-da1e-49e0-9251-515d5997a218
-- title:
--   Eqs. (42)–(44) — a vertex-paired round at $u$ has KL $K_{\mathrm{vertex}}=s\log\frac{s}{s+d}+r\log\frac{r}{r-d}$; at $v$ it has none
-- statement:
--   Let $p,s,d>0$ with $p+s+d<1$ and put $r=1-p-s$. For one vertex-paired round, with states written $(P_0(x),P_1(x))$:
--
--   1. querying $u$ gives the pair distribution $(p,\,s,\,r)$ on the states $(1,1),(0,1),(0,0)$ under the null, and $(p,\,s+d,\,r-d)$ under the alternative;
--   2. its Kullback–Leibler divergence from the null to the alternative is
--   $$
--   K_{\mathrm{vertex}}=s\log\frac{s}{s+d}+r\log\frac{r}{r-d};
--   $$
--   3. querying $v$ gives the same law under both hypotheses, so its divergence is $0$: queries to $v$ carry no information.
--
--   This is the per-round information that the vertex-paired lower bound (36) divides by.
--
--   **Formalization Note** States are passed through the injective code; divergences are Mathlib's `klDiv` in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: KL divergence of two finite laws (a real number) → Mathlib klDiv in ℝ≥0∞, compared with ENNReal.ofReal of the formula; reason: Lean convention; the formula is positive under the hypotheses, so no instance changes
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), proof of Theorem 10.4, eqs. (42)–(44), p.15 (PDF p.17)

import Mathlib
import Definitions.Def_FairReplay_vertexModel

open MeasureTheory InformationTheory

namespace FairReplay

/-- **Eqs. (42)–(44), the KL of one vertex-paired round** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027
submission (manuscript of 2026-11-03, sha256 e23940a0…), proof of Theorem 10.4,
eqs. (42)–(44), p.15 (PDF p.17)): "For vertex-paired replay, querying the potentially changed
endpoint u produces the pair distribution (p, s, r) (42) on states (1, 1), (0, 1), (0, 0) under the
null, and (p, s + d, r − d) (43) under the alternative. Its KL is therefore
K_vertex = s log(s/(s+d)) + r log(r/(r−d)). (44) Queries to v carry no information"

With `r = 1 − p − s`: a round at `u` (action `0`) observes `(P0(u), P1(u))` with masses `p, s, r` on
`(1,1), (0,1), (0,0)` under the null and `p, s + d, r − d` under the alternative, and the KL divergence
from the null to the alternative is `s log(s/(s + d)) + r log(r/(r − d))`. A round at `v` (action
`1`) has the same law under both hypotheses, so its KL divergence is `0`.

**Formalization Note** States are ordered `(P0(x), P1(x))` and passed through the injective code
`obsCode`. KL divergences are Mathlib's `klDiv` in `ℝ≥0∞`. -/
theorem eq_42_44 (p s d : ℝ) (hp : 0 < p) (hs : 0 < s) (hd : 0 < d) (hpsd : p + s + d < 1) :
    let r := 1 - p - s
    let μ₀ := (vertexModel p s d false).P 0
    let μ₁ := (vertexModel p s d true).P 0
    μ₀ {obsCode (![true, true] : Fin 2 → Bool)} = ENNReal.ofReal p ∧
      μ₀ {obsCode (![false, true] : Fin 2 → Bool)} = ENNReal.ofReal s ∧
      μ₀ {obsCode (![false, false] : Fin 2 → Bool)} = ENNReal.ofReal r ∧
      μ₁ {obsCode (![true, true] : Fin 2 → Bool)} = ENNReal.ofReal p ∧
      μ₁ {obsCode (![false, true] : Fin 2 → Bool)} = ENNReal.ofReal (s + d) ∧
      μ₁ {obsCode (![false, false] : Fin 2 → Bool)} = ENNReal.ofReal (r - d) ∧
      klDiv μ₀ μ₁ = ENNReal.ofReal (s * Real.log (s / (s + d)) + r * Real.log (r / (r - d))) ∧
      (vertexModel p s d false).P 1 = (vertexModel p s d true).P 1 ∧
      klDiv ((vertexModel p s d false).P 1) ((vertexModel p s d true).P 1) = 0 := by sorry

end FairReplay
