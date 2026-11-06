-- Prove2me | Theorems.Thm_AltRegret_theorem_1
-- name    : AltRegret.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:06:14.778203+00:00
-- url     : https://prove2.me/theorems/4132ffe5-8654-472d-99da-9f9dd230a1fe
-- title:
--   Theorem 1 (Constant alternating regret) — AA-Hedge has $\mathrm{Reg}^T_{\mathrm{Alt}}\le8\log d$ for every $T\ge1$
-- statement:
--   Let $d\in\mathbb N$, let $T\ge1$, and let $c_1,\dots,c_T\in[-1,1]^d$ be any loss sequence, with $c_0=\mathbf 0$. Let $x_1,\dots,x_T$ be the plays of the alternation-aware Hedge algorithm (Algorithm 1, with $\eta=1/8$ and $\beta=1/32$). Then for every comparator $u\in\Delta_d$,
--   $$
--   \sum_{t=1}^{T}(c_{t-1}+c_t)^\top x_t-\sum_{t=1}^{T}(c_{t-1}+c_t)^\top u\le 8\log d ,
--   $$
--   that is, the alternating regret satisfies $\mathrm{Reg}^T_{\mathrm{Alt}}\le8\log d$.
--
--   The bound does not grow with the horizon $T$, and the algorithm does not need to know $T$. The paper also shows that $\Omega(\log d)$ is necessary, so the bound is optimal up to the constant.
--
--   Differences from the source:
--   - encoding: adaptively chosen loss sequence → every loss sequence c with c_t ∈ [−1,1]^d for 1 ≤ t ≤ T; reason: Algorithm 1 is deterministic and x_t depends only on c_1, …, c_{t−1}, so every adaptive adversary produces one fixed sequence and the two quantifications give the same claim
--   - encoding: Reg^T_Alt with min over x ∈ Δ_d → the bound for every comparator u ∈ Δ_d; reason: the minimum over the compact simplex is attained, so the two forms are equivalent; for d = 0 the simplex is empty and the claim is vacuous, as in the paper
--   - encoding: [d], c_0 = 0, log → Fin d, losses read through lossAt, Real.log (natural logarithm); reason: Lean convention; same instances
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, Theorem 1, p.4 (proof p.8)

import Mathlib
import Definitions.Def_AltRegret_play
import Definitions.Def_AltRegret_altRegretAgainst

namespace AltRegret

/-- **Theorem 1 (Constant alternating regret).** Tao–Zheng, arXiv:2608.24731, Theorem 1, p.4:
"For any `T ≥ 1` and adaptive chosen linear loss sequence `c₁, …, c_T ∈ [−1,1]^d`, the
alternation-aware Hedge (AA-Hedge) algorithm (Algorithm 1) over `Δ_d` guarantees that
`Reg^T_Alt ≤ 8 log d`."

For every `d`, every horizon `T ≥ 1`, every loss sequence with `c_t ∈ [−1,1]^d` for
`1 ≤ t ≤ T`, and every comparator `u ∈ Δ_d`, the plays `x_t` of Algorithm 1 (`η = 1/8`,
`β = 1/32`, `c₀ = 0`) satisfy
`∑_{t=1}^T (c_{t−1} + c_t)ᵀx_t − ∑_{t=1}^T (c_{t−1} + c_t)ᵀu ≤ 8 log d`.

**Formalization Note.** "`Reg^T_Alt ≤ 8 log d`" with the minimum over `Δ_d` in (1) is stated for
every comparator `u ∈ Δ_d`. The adversary is adaptive, but Algorithm 1 is deterministic and `x_t`
depends only on `c₁, …, c_{t−1}`, so every adaptive adversary produces one fixed sequence and
quantifying over all sequences is the same claim. `Real.log` is the natural logarithm. For
`d = 0` the simplex is empty and the statement is vacuous. -/
theorem theorem_1 {d : ℕ} (T : ℕ) (hT : 1 ≤ T) (c : ℕ → Fin d → ℝ)
    (hc : ∀ t, 1 ≤ t → t ≤ T → ∀ i, c t i ∈ Set.Icc (-1 : ℝ) 1)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    altRegretAgainst (play (1 / 8) (1 / 32) c) c T u ≤ 8 * Real.log d := by sorry

end AltRegret
