-- Prove2me | Theorems.Thm_BesbesZeevi_Nonparametric_nonparametric_regret_bound
-- name    : BesbesZeevi.Nonparametric.nonparametric_regret_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:51:46.500043+00:00
-- url     : https://prove2.me/theorems/061f00d6-f553-432a-b0e1-2faceb5d529b
-- title:
--   Proposition 1: Algorithm 1 has regret $\sup_{\lambda\in\mathcal L}\mathcal R^\pi_n\le C(\log n)^{1/2}/n^{1/4}$
-- statement:
--   Let $0<\underline p<\overline p$, let $p_\infty>0$ be the off price, and let $x,T>0$. Let $\mathcal L=\mathcal L(M,\underline K,\overline K,m)$ be the class of regular demand functions satisfying Assumption 1. Choose tuning sequences with $\tau_n\asymp n^{-1/4}$ and $\kappa_n\asymp n^{1/4}$ (with $\tau_n\in(0,T]$ and $\kappa_n$ a positive integer), and let $\pi_n=\pi(\tau_n,\kappa_n)$ be Algorithm 1 run in the market of size $n$. That market has inventory $nx$ and demand $n\lambda$, with demand driven by a unit-rate Poisson process.
--
--   Then there is a finite constant $C>0$ such that for all $n\ge2$,
--
--   $$
--   \sup_{\lambda\in\mathcal L}\mathcal R^\pi_n(x,T;\lambda)\ \le\ \frac{C(\log n)^{1/2}}{n^{1/4}}.
--   $$
--
--   The constant $C$ depends on the class parameters, on $x$, $T$, the price bounds and the tuning, but not on $\lambda$, $n$ or the probability space. In particular, the policies are asymptotically optimal: the worst-case regret over the class tends to $0$.
--
--   **Formalization Note** The paper states (13) for all $n\ge1$. At $n=1$ the right side is $0$, which would claim zero regret, so the statement here is for $n\ge2$; every finite range of $n$ is absorbed into $C$. The supremum over $\mathcal L$ is rendered as a bound for every $\lambda\in\mathcal L$, with $C$ chosen before $\lambda$ and $n$. The asymptotic-optimality clause (12) is not stated separately. The relation $\asymp$ is rendered with explicit constants $0<c\le c'$ (see the `Tuning` structure). The inventory is $\lfloor nx\rfloor$ units.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 12 (PDF 14), Proposition 1, eq. (13)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_BesbesZeevi_Nonparametric_Model
import Definitions.Def_BesbesZeevi_Nonparametric_Algorithm

open MeasureTheory ProbabilityTheory ProcessingNetworks.Stability

namespace BesbesZeevi.Nonparametric

/-- Proposition 1, p. 12: under Assumption 1, with `τ_n ≍ n^{-1/4}`, `κ_n ≍ n^{1/4}` and
`π_n = π(τ_n, κ_n)` given by Algorithm 1,
`sup_{λ ∈ 𝓛} R^π_n(x, T; λ) ≤ C (log n)^{1/2} / n^{1/4}` for some finite positive constant `C`.
Stated for `n ≥ 2` (at `n = 1` the printed right side is `0`). -/
theorem nonparametric_regret_bound (P : PriceSet) (L : DemandClass) (x T : ℝ) (hx : 0 < x) (hT : 0 < T)
    (c c' : ℝ) (τ : ℕ → ℝ) (κ : ℕ → ℕ) (htune : Tuning T c c' τ κ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type*) [MeasureSpace Ω] (N : ℝ → Ω → ℕ), IsPoissonProcess N 1 →
      ∀ n : ℕ, 2 ≤ n → ∀ lam : ℝ → ℝ, L.Mem P lam →
        regret P lam x T n (τ n) (κ n) N ≤ C * Real.sqrt (Real.log n) / (n : ℝ) ^ (1 / 4 : ℝ) := by sorry

end BesbesZeevi.Nonparametric
