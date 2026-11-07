-- Prove2me | Theorems.Thm_DraftPoA_corollary_3_4_parameters
-- name    : DraftPoA.corollary_3_4_parameters
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:16.049191+00:00
-- url     : https://prove2.me/theorems/d4e6992c-a59a-4e54-be1f-015f2160b69e
-- title:
--   Proof of Corollary 3.4: the choice $\rho=\ln m/(\ln\ln m)^2$, $\varepsilon=1/\ln\ln m$ for $m\ge10^{2407}$
-- statement:
--   Write $\ell_2=\ln\ln m$ and $\ell_3=\ln\ln\ln m$, and let $m\ge10^{2407}$. Then $\ell_3\ge1$ and $4\ell_3\le\ell_2$. With $\rho=\ln m/\ell_2^2$ and $\varepsilon=1/\ell_2$ one has $\ln\rho=\ell_2-2\ell_3$, $\ln(m/\varepsilon)=\ln m+\ell_3$, $\rho>1$, $0<\varepsilon\le1/2$,
--
--   $$\frac{\lceil\log_\rho(m/\varepsilon)\rceil+1+\rho}{1-\varepsilon}\ \le\ \Bigl(1+\frac{13\,\ell_3}{\ell_2}\Bigr)\frac{\ln m}{\ell_2}+3,$$
--
--   and $2/(1-\varepsilon)\le4$.
--
--   Combined with Theorem 3.3 these give Corollary 3.4: the continuous-bid bound and, on a grid, the loss $4m\delta$.
--
--   Differences from the source: none.
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), proof of Corollary 3.4, App. A.4, pp.18–19 (PDF 19–20)

import Mathlib

namespace DraftPoA

/-- Proof of Corollary 3.4, App. A.4, pp.18–19 (PDF 19–20) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

Write `ℓ₂ = ln ln m`, `ℓ₃ = ln ln ln m`. For `m ≥ 10^2407`: `ℓ₃ ≥ 1` and `4ℓ₃ ≤ ℓ₂`; with
`ρ = ln m/ℓ₂²` and `ε = 1/ℓ₂`, `ln ρ = ℓ₂ − 2ℓ₃`, `ln(m/ε) = ln m + ℓ₃`, `ρ > 1`, `ε ∈ (0, 1/2]`, the
parameter value of Theorem 3.3 satisfies
`(⌈log_ρ(m/ε)⌉ + 1 + ρ)/(1 − ε) ≤ (1 + 13ℓ₃/ℓ₂) ln m/ℓ₂ + 3`, and `2/(1 − ε) ≤ 4`.

**Formalization Note.** Real analysis only; `10 ^ 2407 ≤ m` is a hypothesis on a natural number. -/
theorem corollary_3_4_parameters (m : ℕ) (hm : 10 ^ 2407 ≤ m) :
    let l2 := Real.log (Real.log m)
    let l3 := Real.log (Real.log (Real.log m))
    let ρ := Real.log m / l2 ^ 2
    let ε := 1 / l2
    1 ≤ l3 ∧ 4 * l3 ≤ l2 ∧ Real.log ρ = l2 - 2 * l3 ∧ Real.log ((m : ℝ) / ε) = Real.log m + l3 ∧
    1 < ρ ∧ 0 < ε ∧ ε ≤ 1 / 2 ∧
    ((⌈Real.logb ρ ((m : ℝ) / ε)⌉₊ : ℝ) + 1 + ρ) / (1 - ε) ≤
      (1 + 13 * l3 / l2) * (Real.log m / l2) + 3 ∧
    2 / (1 - ε) ≤ 4 := by sorry

end DraftPoA
