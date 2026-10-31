-- Prove2me | Theorems.Thm_DRBaseline_proposition_2
-- name    : DRBaseline.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:43.530621+00:00
-- url     : https://prove2.me/theorems/362265cd-d694-4e9b-af8c-9e78025fa8d3
-- title:
--   Proposition 2: the optimal baseline increases in $\Delta c$ below $c_A$ and decreases above
-- statement:
--   Let $\Omega>0$, $c_s>0$, $\rho\in(0,1]$, $c_A(\Omega,c_s)=5\Omega c_s/2$, and $s$ any best-response selection. Let $0<\Delta c_1\le\Delta c_2$ and let $(b_1,r_1)$, $(b_2,r_2)$ be the least-rebate maximizers of $C$ at $\Delta c_1$, $\Delta c_2$. Then
--
--   1. if $\Delta c_2\le c_A$, then $b_1\le b_2$;
--   2. if $c_A\le\Delta c_1$, then $b_2\le b_1$.
--
--   Contrary to the intuition that a higher stake calls for a higher baseline, beyond $c_A$ the firm lowers the baseline while it keeps raising the rebate.
--
--   Differences from the source:
--
--   - generalization: increases in ∆c if ∆c < cA(·) → increasing on 0 < Δc ≤ c_A; reason: b∗ is continuous at c_A (both formulas give 3Ω/2); specializes to the open range
--   - reading: the baseline b∗ = arg max → the least-rebate maximizer; reason: (b∗, r∗) is not unique for Δc ≥ 4Ωc_s
--   - encoding: increases / decreases → b₁ ≤ b₂ (resp. b₂ ≤ b₁) for Δc₁ ≤ Δc₂; reason: weak sense (p.11)
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Proposition 2, p.16; proof pp.OA2–OA3

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsLeastRebateOptimal

namespace DRBaseline

/-- **Proposition 2: the optimal baseline increases in `Δc` below `c_A` and decreases above.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Proposition 2, p.16; proof pp.OA2–OA3 (`c_A(Ω, c_s) = c_{A1} = 5Ωc_s/2`).

Let `Ω > 0`, `c_s > 0`, `ρ ∈ (0, 1]` and `s` any best-response selection. For least-rebate
maximizers `(b₁, r₁)` at `Δc₁` and `(b₂, r₂)` at `Δc₂` with `0 < Δc₁ ≤ Δc₂`:
1. if `Δc₂ ≤ c_A`, then `b₁ ≤ b₂`;
2. if `c_A ≤ Δc₁`, then `b₂ ≤ b₁`.

**Formalization Note** "Increasing"/"decreasing" are weak (p.11). The page's "if ∆c < cA(·)" is
stated on the closed range `Δc ≤ c_A`; at `c_A` itself both items hold, as `b∗` is continuous
there. -/
theorem proposition_2 (Ω cs ρ : ℝ) (hΩ : 0 < Ω) (hcs : 0 < cs) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) (Δc₁ Δc₂ b₁ r₁ b₂ r₂ : ℝ)
    (hΔ₁ : 0 < Δc₁) (hΔ : Δc₁ ≤ Δc₂) (h₁ : IsLeastRebateOptimal Ω ρ Δc₁ s b₁ r₁)
    (h₂ : IsLeastRebateOptimal Ω ρ Δc₂ s b₂ r₂) :
    (Δc₂ ≤ 5 * Ω * cs / 2 → b₁ ≤ b₂) ∧ (5 * Ω * cs / 2 ≤ Δc₁ → b₂ ≤ b₁) := by sorry

end DRBaseline
