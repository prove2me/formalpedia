-- Prove2me | Theorems.Thm_DRBaseline_lemma_3
-- name    : DRBaseline.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:43:26.760781+00:00
-- url     : https://prove2.me/theorems/eaf056bb-bde4-48ac-8128-28f5af4a6c0c
-- title:
--   Lemma 3: at $b=\Lambda$ the program is offered iff $\Delta c>c_0$, and $r_0$ increases in $\Delta c$
-- statement:
--   Let $0<\Lambda<\Omega$, $c_s>0$, $\rho\in(0,1]$, $c_0(\Lambda,c_s)=\Lambda c_s/2$, and $s$ any best-response selection. When the baseline is the average non-event demand $b=\Lambda$:
--
--   1. for every $\Delta c>0$ and every optimal rebate $r_0$, the program is offered ($r_0>0$) if and only if $\Delta c>c_0$;
--   2. the optimal rebate increases in $\Delta c$: if $0<\Delta c_1\le\Delta c_2$ and $r_1$, $r_2$ are optimal rebates at $\Delta c_1$, $\Delta c_2$, then $r_1\le r_2$.
--
--   For a small cost difference the rebate payments and the overestimation penalty outweigh the procurement savings, and the firm offers nothing.
--
--   Differences from the source:
--
--   - generalization: offers a program only if ∆c > c0 → r₀ > 0 if and only if Δc > c₀; reason: the iff contains the page's 'only if'; the converse is the second to fourth branches of p.OA2
--   - encoding: offers a demand-response program → r₀ > 0; reason: a zero rebate is no program
--   - encoding: r0 increases in ∆c → optimal rebates at Δc₁ ≤ Δc₂ satisfy r₁ ≤ r₂; reason: weak sense (p.11); stated for every optimal rebate
-- source:
--   Agrawal, Yücel, Design of Electricity Demand-Response Programs, manuscript of May 26, 2021, Lemma 3, p.15; proof p.OA2

import Mathlib
import Definitions.Def_DRBaseline_IsBestResponse
import Definitions.Def_DRBaseline_IsNormalUseOptimal

namespace DRBaseline

/-- **Lemma 3: with `b = Λ` the program is offered exactly when `Δc > c₀`, and `r₀` increases
in `Δc`.**
Agrawal, Yücel, *Design of Electricity Demand-Response Programs*, manuscript of May 26, 2021, Lemma 3, p.15; proof p.OA2.

Let `0 < Λ < Ω`, `c_s > 0`, `ρ ∈ (0, 1]`, `c₀(Λ, c_s) = Λc_s/2`, and `s` any best-response
selection.
1. For every `Δc > 0` and every optimal normal-use rebate `r₀`: `r₀ > 0` (the program is
   offered) if and only if `Δc > c₀`.
2. If `0 < Δc₁ ≤ Δc₂` and `r₁`, `r₂` are optimal normal-use rebates at `Δc₁`, `Δc₂`, then
   `r₁ ≤ r₂`.

**Formalization Note** The page says "only if"; the Lean states the iff, which contains it.
"Offers a program" is read as a positive rebate. -/
theorem lemma_3 (Ω Λ cs ρ : ℝ) (hΛ : 0 < Λ) (hΛΩ : Λ < Ω) (hcs : 0 < cs) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (s : ℝ → ℝ → ℝ → ℝ) (hs : IsBestResponse Ω cs s) :
    (∀ Δc r₀ : ℝ, 0 < Δc → IsNormalUseOptimal Ω Λ ρ Δc s r₀ → (0 < r₀ ↔ Λ * cs / 2 < Δc)) ∧
    (∀ Δc₁ Δc₂ r₁ r₂ : ℝ, 0 < Δc₁ → Δc₁ ≤ Δc₂ → IsNormalUseOptimal Ω Λ ρ Δc₁ s r₁ →
      IsNormalUseOptimal Ω Λ ρ Δc₂ s r₂ → r₁ ≤ r₂) := by sorry

end DRBaseline
