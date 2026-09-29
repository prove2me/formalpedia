-- Prove2me | Theorems.Thm_EthierKurtz_exclusion_cylinder_range_dense
-- name    : EthierKurtz.exclusion_cylinder_range_dense
-- status  : Proved
-- author  : @Gabewhigham
-- created : 2026-09-27T18:57:57.899955+00:00
-- url     : https://prove2.me/theorems/82a5685e-3c8e-454c-b12b-60a6682acc6b
-- title:
--   Range condition for the exclusion generator on cylinder functions
-- statement:
--   Let $S$ be countable, $E=\{0,1\}^S$ (product topology), and let $c(i,j,\cdot)\in C(E)$, $\gamma(i,j)\ge 0$ satisfy the hypotheses of Ethier–Kurtz Chapter 8, Theorem 3.6 as formalized in `EthierKurtz.exclusion_feller_generation`: $0\le c(i,j,\eta)\le\gamma(i,j)$, $c(i,i,\cdot)=0$, $c$ and $\gamma$ symmetric in $(i,j)$, $\sup_i\sum_j\gamma(i,j)<\infty$, and $\sum_k\|\Delta_k c(i,j,\cdot)\|\le K\gamma(i,j)$ where $\Delta_k$ is the single-site flip difference. Let $\Omega f(\eta)=\sum_{i,j}c(i,j,\eta)\,(f(\eta^{ij})-f(\eta))$ be the exclusion operator, where $\eta^{ij}$ exchanges the values at $i$ and $j$.
--
--   **Claim.** There is $r>0$ such that
--
--   $$\{\,rf-\Omega f : f\in C(E)\text{ depends on finitely many coordinates}\,\}$$
--
--   is dense in $C(E)$. (Every such cylinder function lies in the weighted domain of $\Omega$, and $\Omega f$ is continuous.)
--
--   This is the range condition in the proof of Theorem 3.6: one solves $r u_n-\Omega_n u_n=h$ for finite truncations $\Omega_n$ (a finite-state generator acting on functions of the coordinates in a finite set $F_n$, with frozen outside coordinates), uses the Liggett-type estimate $r\|\Delta_k u_n\|\le\|\Delta_k h\|+\sum_l\Gamma_{kl}\|\Delta_l u_n\|$ with a matrix $\Gamma$ of bounded column sums (controlled by $M$ and $K$), and shows $(\Omega-\Omega_n)u_n\to0$ uniformly for $r$ large.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, proof of Theorem 3.6, equations (3.26)–(3.29), printed p. 381 (PDF p. 390); cf. the estimates of Section 8.3 preceding it.

import Definitions.Def_EthierKurtz_exclusionGraph
import Definitions.Def_EthierKurtz_spinVariation

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Range condition for the exclusion generator on cylinder functions: for some
`r > 0`, the functions `r f - Ω f` with `f` a continuous function depending on
finitely many coordinates are dense in `C(S → Bool)`. -/
theorem exclusion_cylinder_range_dense (S : Type*) [Countable S]
    (c : S → S → C(S → Bool, ℝ)) (γ : S → S → ℝ)
    (hc_nonneg : ∀ i j η, 0 ≤ c i j η)
    (hγ_nonneg : ∀ i j, 0 ≤ γ i j)
    (hdiag : ∀ i, c i i = 0)
    (hc_symm : ∀ i j, c i j = c j i)
    (hdom : ∀ i j η, c i j η ≤ γ i j)
    (hγ_symm : ∀ i j, γ i j = γ j i)
    (hrows : ∃ M : ℝ, ∀ i, Summable (γ i) ∧ (∑' j, γ i j) ≤ M)
    (hinfluence : ∃ K : ℝ, ∀ i j,
      Summable (spinVariation (c i j)) ∧
        (∑' k, spinVariation (c i j) k) ≤ K * γ i j) :
    ∃ r : ℝ, 0 < r ∧
      Dense ((fun fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) => r • fg.1 - fg.2) ''
        {fg : C(S → Bool, ℝ) × C(S → Bool, ℝ) |
          fg ∈ exclusionGraph c γ ∧ ∃ F : Finset S, ∀ η ξ : S → Bool,
            (∀ i ∈ F, η i = ξ i) → fg.1 η = fg.1 ξ}) := by sorry
