-- Prove2me | Theorems.Thm_Erdos142_green_tao_four
-- name    : Erdos142.green_tao_four
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:41:04.359497+00:00
-- url     : https://prove2.me/theorems/febec46b-32c4-4563-b277-697ccf1defd0
-- title:
--   Green–Tao (2017): $r_4(N) \ll N(\log N)^{-c}$
-- statement:
--   There is a constant $c > 0$ such that, for all sufficiently large $N$,
--
--   $$r_4(N) \;\le\; \frac{N}{(\log N)^{c}} .$$
--
--   This is the polylogarithmic bound of Green and Tao for four-term progressions. It improved on Gowers's $r_4(N) \ll N(\log\log N)^{-c}$ and on their own earlier bound $N\exp(-c\sqrt{\log\log N})$, and remains the best known upper bound for $k = 4$; the authors describe it as the limit of their method.
--
--   The four-term case is the first in which the Fourier-analytic machinery of Roth's theorem is insufficient and quadratic Fourier analysis is required: the relevant obstruction to uniformity is correlation with a quadratic phase rather than a linear one, so the argument runs through the inverse theorem for the Gowers $U^3$-norm and an arithmetic regularity lemma. Note that this bound is still weaker than the mission's goal at $k = 4$, which asks for $o(N/\log N)$: the exponent $c$ produced here is small and not known to exceed $1$.
--
--   **Formalization Note.** The implied constant of $\ll$ is absorbed by shrinking $c$, so the displayed form with $\exists c > 0$ and an eventual inequality is equivalent to the paper's statement and fixes no arbitrary constant.
-- source:
--   B. Green and T. Tao, New bounds for Szemeredi's theorem, III: A polylogarithmic bound for r_4(N), Mathematika 63 (2017), 944-1040, arXiv:1705.01703, https://arxiv.org/abs/1705.01703. Cited as the best known upper bound for k=4 on Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem green_tao_four :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 4 N : ℝ) ≤ (N : ℝ) / (Real.log N) ^ c := by sorry

end Erdos142
