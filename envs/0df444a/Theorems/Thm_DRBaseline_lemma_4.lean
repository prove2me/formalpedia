-- Prove2me | Theorems.Thm_DRBaseline_lemma_4
-- name    : DRBaseline.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:52.240093+00:00
-- url     : https://prove2.me/theorems/1312e861-098c-4885-9b5a-a30ed1a20bfd
-- title:
--   Lemma 4: with both instruments the program is always offered, and $r^*$ increases in $\Delta c$
-- statement:
--   Let $\Omega>0$, $c_s>0$, $\rho\in(0,1]$ and $s$ any best-response selection.
--
--   1. For every $\Delta c>0$ and every maximizer $(b,r)$ of $C$ over $b,r\ge0$: $r>0$ and $C(b,r)>0$; the firm offers the program however small the cost difference.
--   2. If $0<\Delta c_1\le\Delta c_2$ and $(b_1,r_1)$, $(b_2,r_2)$ are the least-rebate maximizers at $\Delta c_1$, $\Delta c_2$, then $r_1\le r_2$.
--
--   Adjusting the baseline lets the firm keep the overestimation penalty below the procurement savings for every $\Delta c$.
--
--   Differences from the source:
--
--   - generalization: the firm (choosing (b∗, r∗)) should always offer the program → every maximizer has r > 0 and C(b, r) > 0; reason: it includes the least-rebate maximizer (b∗, r∗)
--   - reading: r∗ increases in ∆c → for the least-rebate maximizer; reason: (b∗, r∗) is not unique for Δc ≥ 4Ωc_s; other maximizers have arbitrarily large rebates
--   - encoding: should always offer the demand-response program → r > 0 and C(b, r) > 0; reason: a program with zero rebate or no savings is not offered
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Lemma 4, p.15; proof pp.OA2–OA3

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal

namespace DRBaseline

/-- **Lemma 4: with both instruments the program is always offered, and `r∗` increases in
`Δc`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Lemma 4, p.15; proof pp.OA2–OA3.

Let `Ω > 0`, `c_s > 0`, `ρ ∈ (0, 1]` and `s` any best-response selection.
1. For every `Δc > 0` and every maximizer `(b, r)` of `C` over `b, r ≥ 0`: `r > 0` and
   `C(b, r) > 0`.
2. If `0 < Δc₁ ≤ Δc₂` and `(b₁, r₁)`, `(b₂, r₂)` are the least-rebate maximizers at `Δc₁`,
   `Δc₂`, then `r₁ ≤ r₂`.

**Formalization Note** "Offer the program" is read as a positive rebate with positive net
savings, and is stated for every maximizer. Monotonicity is for the least-rebate maximizer
`(b∗, r∗)` the page selects (for `Δc ≥ 4Ωc_s` other maximizers have arbitrarily large
rebates). -/
theorem lemma_4 (Ω cs ρ : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) :
    (∀ Δc b r : ℝ, 0 < Δc → IsFirmOptimal Ω ρ Δc s b r →
      0 < r ∧ 0 < netSavings Ω ρ Δc s b r) ∧
    (∀ Δc₁ Δc₂ b₁ r₁ b₂ r₂ : ℝ, 0 < Δc₁ → Δc₁ ≤ Δc₂ →
      IsLeastRebateOptimal Ω ρ Δc₁ s b₁ r₁ → IsLeastRebateOptimal Ω ρ Δc₂ s b₂ r₂ →
      r₁ ≤ r₂) := by sorry

end DRBaseline
