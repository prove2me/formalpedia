-- Prove2me | Theorems.Thm_DRBaseline_lemma_2
-- name    : DRBaseline.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:37.68785+00:00
-- url     : https://prove2.me/theorems/fc8bc2ab-df7d-4e9a-9802-e72cfed24245
-- title:
--   Lemma 2: $X$ increases in $b$ and $r$; $X_o$ increases in $b$; $X_u$ increases in $r$ and decreases in $b\ge B$
-- statement:
--   Let $\Omega>0$, $c_s>0$, $\rho\in(0,1]$ and let $s$ be any best-response selection. For baselines and rebates in $[0,\infty)$:
--
--   1. the expected actual demand reduction $X(b,r)$ is increasing in $r$ and increasing in $b$;
--   2. the expected overestimation $X_o(b)$ does not depend on the rebate and is increasing in $b$;
--   3. the expected underestimation $X_u(b,r)$ is increasing in $r$, and decreasing in $b$ on $b\ge B(\Omega,r,c_s)$.
--
--   "Increasing" and "decreasing" are meant in the weak sense. A higher baseline raises the actual reduction but also the overcompensation, which is the firm's trade-off.
--
--   Differences from the source:
--
--   - encoding: X_o(b) is independent of the rebate → X_o takes no rebate argument; reason: the definition on p.13 has none
--   - encoding: X_o(b) = ρ∫_0^b (b − ω) f(ω) dω → the integral over (0, min(b, 2Ω)]; reason: f = 0 above 2Ω (p.7); the same value for b ≤ 2Ω
--   - encoding: X_u(b,r) = ρ∫_b^{ω1} (ω − b) f(ω) dω → the set integral over {b ≤ ω ≤ ω₁}; reason: the page's region 'b ≤ ω ≤ ω1(·)'; it is empty, so X_u = 0, when b > ω₁, where an oriented integral would make the third bullet false
--   - encoding: increases / decreases → weak inequalities between values at b ≤ b′ or r ≤ r′, over b, r ≥ 0; reason: p.11: the terms are used in the weak sense; the firm's domain
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Lemma 2, p.14; proof p.OA1

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_demandReduction
import Definitions.Def_DRBaseline_overestimation
import Definitions.Def_DRBaseline_underestimation
import Definitions.Def_DRBaseline_baselineB

namespace DRBaseline

/-- **Lemma 2: comparative statics of `X`, `X_o`, `X_u`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Lemma 2, p.14; proof p.OA1.

For every best-response selection `s` (with `b, r ≥ 0` throughout):
1. `X(b, r)` is increasing in `r` and increasing in `b`;
2. `X_o(b)` (which does not involve `r`) is increasing in `b`;
3. `X_u(b, r)` is increasing in `r`, and decreasing in `b` on `b ≥ B(Ω, r, c_s)`.
"Increasing" and "decreasing" are weak (p.11).

**Formalization Note** `X_o` takes no rebate argument, which is the "independent of the rebate"
clause. `X_u` is the set integral over `{b ≤ ω ≤ ω₁}` and `X_o` cuts the density at `2Ω`, so
both are meaningful for `b > 2Ω` as well. -/
theorem lemma_2 (Ω cs ρ : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) :
    (∀ b r r' : ℝ, 0 ≤ b → 0 ≤ r → r ≤ r' →
      demandReduction Ω ρ s b r ≤ demandReduction Ω ρ s b r') ∧
    (∀ b b' r : ℝ, 0 ≤ b → b ≤ b' → 0 ≤ r →
      demandReduction Ω ρ s b r ≤ demandReduction Ω ρ s b' r) ∧
    (∀ b b' : ℝ, 0 ≤ b → b ≤ b' → overestimation Ω ρ b ≤ overestimation Ω ρ b') ∧
    (∀ b r r' : ℝ, 0 ≤ b → 0 ≤ r → r ≤ r' →
      underestimation Ω cs ρ b r ≤ underestimation Ω cs ρ b r') ∧
    (∀ b b' r : ℝ, 0 ≤ r → baselineB Ω cs r ≤ b → b ≤ b' →
      underestimation Ω cs ρ b' r ≤ underestimation Ω cs ρ b r) := by sorry

end DRBaseline
