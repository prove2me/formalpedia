-- Prove2me | Theorems.Thm_ForecastComp_IELF_ielf_select_lower_bound
-- name    : ForecastComp.IELF.ielf_select_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:51.524975+00:00
-- url     : https://prove2.me/theorems/932a4367-7e66-485e-82ce-be1e0972a242
-- title:
--   Proof of Theorem 7 (Appendix M), p. 36 — I-ELF selects i with probability ≥ 1 − 2(n−1)e^{−mΔ²/(2(n−1)²)}
-- statement:
--   Let $n\ge2$, let $R$ take values in $[0,1]$ on $[0,1]$, let the outcomes be independent with marginals $\theta\in[0,1]^m$, and let all reports lie in $[0,1]$. If forecaster $i$'s expected score exceeds every other forecaster's by at least $\Delta>0$, i.e. $R(y_i,\theta)-R(y_j,\theta)\ge\Delta$ for all $j\ne i$, then
--   $$\Pr_{X\sim\theta}\big(M_{\text{I-ELF}^R}(y_1,\dots,y_n,X)=i\big)\ge1-2(n-1)\,e^{-\frac{m\Delta^2}{2(n-1)^2}}.$$
--   In particular, the probability is at least $\pi\in[0,1)$ once $m\ge\frac{2(n-1)^2}{\Delta^2}\ln\frac{2(n-1)}{1-\pi}$, which yields limit accuracy.
--
--   **Formalization Note** The paper writes $M_{\text{ELF}^R}$ in this display; the mechanism meant (and formalized) is I-ELF.
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 36, proof of Theorem 7 (Appendix M), final display

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Proof of Theorem 7 (Appendix M), p. 36: if forecaster `i`'s expected score exceeds every
other forecaster's by at least `Δ > 0`, then under independent outcomes I-ELF selects `i` with
probability at least `1 − 2(n−1) e^{−mΔ²/(2(n−1)²)}`. -/
theorem ielf_select_lower_bound {m n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ)
    (hbdd : IsUnitBounded R)
    (θ : Fin m → ℝ) (hθ : ∀ k, θ k ∈ Set.Icc (0:ℝ) 1)
    (y : Fin n → Fin m → ℝ) (hy : ∀ j k, y j k ∈ Set.Icc (0:ℝ) 1)
    (i : Fin n) (Δ : ℝ) (hΔ : 0 < Δ)
    (hgap : ∀ j, j ≠ i → Δ ≤ avgScore R θ (y i) - avgScore R θ (y j)) :
    1 - 2 * ((n:ℝ) - 1) * Real.exp (-((m:ℝ) * Δ ^ 2) / (2 * ((n:ℝ) - 1) ^ 2)) ≤
      ielfSelProbIndep R θ y i := by sorry

end ForecastComp.IELF
