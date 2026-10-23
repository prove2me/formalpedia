-- Prove2me | Theorems.Thm_ForecastComp_IELF_prob_wins_ge_le
-- name    : ForecastComp.IELF.prob_wins_ge_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:42.927734+00:00
-- url     : https://prove2.me/theorems/eb5f801c-b05c-432b-8af2-d3adb1095516
-- title:
--   Proof of Theorem 7 (Appendix M), p. 36 — Pr(z_j ≥ z_i) ≤ 2e^{−mΔ²/(2(n−1)²)}
-- statement:
--   Let $n\ge2$, let $R$ take values in $[0,1]$ on $[0,1]$, let the outcomes be independent with marginals $\theta\in[0,1]^m$, and let all reports lie in $[0,1]$. Let $i\ne j$ be forecasters and $\Delta>0$ with $R(y_i,\theta)-R(y_j,\theta)\ge\Delta$. Writing $z_l$ for the number of I-ELF event lotteries won by forecaster $l$,
--   $$\Pr(z_j\ge z_i)\le2e^{-\frac{m\Delta^2}{2(n-1)^2}},$$
--   where the probability is over the outcomes and the event lotteries.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 36, proof of Theorem 7 (Appendix M)

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Proof of Theorem 7 (Appendix M), p. 36: if forecaster `i`'s expected score exceeds `j`'s by
at least `Δ > 0`, then under independent outcomes the probability that `j` wins at least as many
event lotteries as `i` is at most `2 e^{−mΔ²/(2(n−1)²)}`. -/
theorem prob_wins_ge_le {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k, y j k ∈ Set.Icc (0:ℝ) 1)
    (i j : Fin n) (hij : i ≠ j) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : Δ ≤ avgScore R θ (y i) - avgScore R θ (y j)) :
    probWinsGe R θ y j i ≤
      2 * Real.exp (-((m:ℝ) * Δ ^ 2) / (2 * ((n:ℝ) - 1) ^ 2)) := by sorry

end ForecastComp.IELF
