-- Prove2me | Theorems.Thm_Erdos142_kelley_meka
-- name    : Erdos142.kelley_meka
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:40:40.515828+00:00
-- url     : https://prove2.me/theorems/326cfe4b-97d3-49de-9313-7362d1167165
-- title:
--   Kelley–Meka (2023): $r_3(N) \le N e^{-c(\log N)^{1/12}}$
-- statement:
--   There is a constant $c > 0$ such that, for all sufficiently large $N$,
--
--   $$r_3(N) \;\le\; N\,e^{-c(\log N)^{1/12}} .$$
--
--   This is the theorem of Kelley and Meka: a subset of $\{1,\dots,N\}$ of size at least $N\exp(-c(\log N)^{1/12})$ must contain a non-trivial three-term arithmetic progression. It was the first bound of quasipolynomial type for the three-term problem, superseding the logarithmic-barrier bound $r_3(N) \ll N(\log N)^{-1-c}$ of Bloom and Sisask, itself the first improvement past $N/\log N$.
--
--   Set against Behrend's lower bound $N\exp(-4\sqrt{\log N})$, this result narrows the three-term problem to determining the exponent of $\log N$ in the exponential, somewhere between $1/12$ and $1/2$; the constant $1/2$ is widely believed to be the truth. Kelley and Meka's argument rests on a sifting technique together with almost-periodicity results for convolutions, and it is the only route currently known to a density increment with polynomial dependence on the density.
--
--   **Formalization Note.** The implied constant of the usual $\ll$ notation is absorbed into the statement: for large $N$ any constant multiple can be traded for a slightly smaller $c$, so the displayed form with $\exists c > 0$ and an eventual inequality is equivalent to the paper's, and fixes no arbitrary constant.
-- source:
--   Z. Kelley and R. Meka, Strong bounds for 3-progressions, arXiv:2302.05537, https://arxiv.org/abs/2302.05537 (abstract: if A is a subset of {1,...,N} with no non-trivial three-term arithmetic progression then |A| <= exp(-c(log N)^{1/12}) N). Cited as the best known upper bound for k=3 on Erdős Problem #142, https://www.erdosproblems.com/142 (cited there as [Er80, p.92], [Er81, p.4], [Er97c], [Va99, 1.27])

import Mathlib
import Definitions.Def_Erdos142Basic

namespace Erdos142

theorem kelley_meka :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      (r 3 N : ℝ) ≤ (N : ℝ) * Real.exp (-c * (Real.log N) ^ ((1 : ℝ) / 12)) := by sorry

end Erdos142
