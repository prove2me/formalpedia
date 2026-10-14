-- Prove2me | Theorems.Thm_CPDNetworks_Lower_display_p37
-- name    : CPDNetworks.Lower.display_p37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:37.290885+00:00
-- url     : https://prove2.me/theorems/e7849842-8916-4941-ae0b-3bd0dd6169bc
-- title:
--   Display, p. 37 — the second moment is at most exp(½μ_n²n(n−1)/(1−2μ_n(n−1))) when μ_n(n−1) < 1/2
-- statement:
--   Under the hypotheses of Step 1 (with $R\sqrt T\le\varepsilon_n\omega_n$), let $\mu_n$ be as in display (27) and assume $\mu_n(n-1)<1/2$. Then
--   $$\mathrm E_0\Big[\frac{dp^\tau_{n,1}}{dp_{n,0}}\Big]^2(Y)\ \le\ \mathrm E_\zeta\exp\Big\{\frac12\mu_n\zeta^{\mathsf T}\big(\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n\big)\zeta\Big\}\ \le\ \exp\Big(\frac{\frac12\mu_n^2\,n(n-1)}{1-2\mu_n(n-1)}\Big).$$
--
--   This is the explicit bound on the second moment of the likelihood ratio from which the condition on the energy $R$ in Theorem 2 is read off.
--
--   **Formalization Note** The page states the bound "for any $\mu_n<1/2$" with denominator $1-2\mu_n$. That printed form is false for large $n$: with $\mu_n=0.1$ and $n=1000$ the middle term exceeds $e^{49000}$ while the printed right side is $e^{6244}$. The page applies Step 4 to $A=\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n$ without accounting for $\|A\|_{2\to2}=n-1$; with it (equivalently, Step 4 applied to $A/(n-1)$) the condition becomes $\mu_n(n-1)<1/2$ and the denominator $1-2\mu_n(n-1)$, which is what is stated. $\zeta^{\mathsf T}(\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n)\zeta$ is written as $\sum_{i\ne j}\zeta_i\zeta_j$. The hypotheses $\omega_n\ge4\sqrt{2C_\eta}$, $\omega_n\le(n-1)/2$ are the disclosed additions of Step 1.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 37, proof of Theorem 2, Step 4, first display

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting
import Definitions.Def_CPDNetworks_Lower_Priors

namespace CPDNetworks.Lower

/-- **First display of p. 37** (Enikeeva–Klopp, proof of Theorem 2, Step 4), with the range of
`μ_n` corrected: under the hypotheses of Step 1 and `μ_n(n − 1) < 1/2`,
`E₀[dp^τ_{n,1}/dp_{n,0}]² ≤ E_ζ exp{½μ_n ζᵀ(1_n1_nᵀ − id_n)ζ} ≤ exp(½μ_n²n(n − 1)/(1 − 2μ_n(n − 1)))`.
The paper prints the condition `μ_n < 1/2` and the denominator `1 − 2μ_n`, which drop
`‖1_n1_nᵀ − id_n‖_{2→2} = n − 1`; that printed form is false for large `n`. -/
theorem display_p37 (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hRT : R * Real.sqrt T ≤ epsN α β ω * ω)
    (hμ : 2 * muN n T ω α β R * ((n : ℝ) - 1) < 1) :
    ∑ y : Obs n T, altMix n T τ α β ω R y ^ 2 / nullMix n T α β ω y ≤
        (2 ^ n : ℝ)⁻¹ * ∑ b : Fin n → Bool,
          Real.exp (1 / 2 * muN n T ω α β R *
            ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else sgn b i * sgn b j) ∧
      (2 ^ n : ℝ)⁻¹ * ∑ b : Fin n → Bool,
          Real.exp (1 / 2 * muN n T ω α β R *
            ∑ i : Fin n, ∑ j : Fin n, if i = j then 0 else sgn b i * sgn b j) ≤
        Real.exp (1 / 2 * muN n T ω α β R ^ 2 * n * ((n : ℝ) - 1) /
          (1 - 2 * muN n T ω α β R * ((n : ℝ) - 1))) := by sorry

end CPDNetworks.Lower
