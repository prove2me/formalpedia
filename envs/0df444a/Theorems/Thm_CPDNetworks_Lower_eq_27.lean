-- Prove2me | Theorems.Thm_CPDNetworks_Lower_eq_27
-- name    : CPDNetworks.Lower.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:38.411562+00:00
-- url     : https://prove2.me/theorems/a3d1cc45-13a0-40a4-886b-c2b088210162
-- title:
--   Display (27) — the second moment of the likelihood ratio is at most E_ζ exp(½μ_n Σ_{i≠j} ζ_iζ_j)
-- statement:
--   Under the hypotheses of Step 1 (with $R\sqrt T\le\varepsilon_n\omega_n$), let $p_{n,0}$ and $p^\tau_{n,1}$ be the mixture laws of the observations under the null and alternative priors of the proof of Theorem 2, and let
--   $$\mu_n=\frac{TR^2}{\omega_n}\cdot\frac1{(1-\tilde\rho_n)(n-1)(1-\varepsilon_n)} .$$
--   Then
--   $$\mathrm E_0\Big[\frac{dp^\tau_{n,1}}{dp_{n,0}}\Big]^2(Y)\ \le\ \mathrm E_\zeta\exp\Big(\frac12\mu_n\sum_{i\ne j}\zeta_i\zeta_j\Big),$$
--   where $\zeta$ has i.i.d. Rademacher entries and the sum runs over ordered pairs $i\ne j$.
--
--   The left side is the $\chi^2$-divergence plus one, which enters display (25); the right side is the Laplace transform of a Rademacher chaos, bounded in Step 4.
--
--   **Formalization Note** $\mathrm E_0[(dp^\tau_{n,1}/dp_{n,0})^2]$ is written $\sum_Y p^\tau_{n,1}(Y)^2/p_{n,0}(Y)$, and $\mathrm E_\zeta$ is the average over the $2^n$ sign vectors. The page writes the exponent also as $\frac12\mu_n\zeta^{\mathsf T}(\mathbf 1_n^{\mathsf T}\mathbf 1_n-\mathrm{id}_n)\zeta$, where $\mathbf 1_n\mathbf 1_n^{\mathsf T}$ is meant; the sum over $i\ne j$ states it without that slip. The hypotheses $\omega_n\ge4\sqrt{2C_\eta}$, $\omega_n\le(n-1)/2$ are the disclosed additions of Step 1.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 36, proof of Theorem 2, Step 3, display (27)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting
import Definitions.Def_CPDNetworks_Lower_Priors

namespace CPDNetworks.Lower

/-- **Display (27)** (Enikeeva–Klopp, proof of Theorem 2, Step 3, p. 36): under the hypotheses of
Step 1, the second moment of the likelihood ratio of the mixtures `p^τ_{n,1}` and `p_{n,0}` is at
most `E_ζ exp(½ μ_n Σ_{i≠j} ζ_iζ_j)`, where
`μ_n = (TR²/ω_n) / ((1 − ρ̃_n)(n − 1)(1 − ε_n))` and `E_ζ` is the average over `ζ ∈ {−1, +1}ⁿ`. -/
theorem eq_27 (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hRT : R * Real.sqrt T ≤ epsN α β ω * ω) :
    ∑ y : Obs n T, altMix n T τ α β ω R y ^ 2 / nullMix n T α β ω y ≤
      (2 ^ n : ℝ)⁻¹ * ∑ b : Fin n → Bool,
        Real.exp (1 / 2 * muN n T ω α β R *
          ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else sgn b i * sgn b j) := by sorry

end CPDNetworks.Lower
