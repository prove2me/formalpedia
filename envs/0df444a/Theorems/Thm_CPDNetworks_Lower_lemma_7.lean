-- Prove2me | Theorems.Thm_CPDNetworks_Lower_lemma_7
-- name    : CPDNetworks.Lower.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:50.779055+00:00
-- url     : https://prove2.me/theorems/3a4f1b14-9d13-47f4-9f50-137a03f6dce6
-- title:
--   Lemma 7 — second moments of Bernoulli likelihood ratios: E₀[dp_q/dp₀]² = 1 + ρ_n q²/(1 − ρ_n)
-- statement:
--   Let $\rho_n\in(0,1/2]$ and $q,q_1,q_2\in[-1,1]$. Write $p_0$ for the Bernoulli law with parameter $\rho_n$ and $p_q$ for the Bernoulli law with parameter $\rho_n(1+q)$, with densities $dp_0$, $dp_q$ with respect to counting measure on $\{0,1\}$. For a Bernoulli variable $X\sim p_0$,
--   $$\mathrm E_0\Big[\frac{dp_q}{dp_0}\Big]^2(X)=1+\frac{\rho_n}{1-\rho_n}\,q^2,\qquad \mathrm E_0\Big[\frac{dp_{q_1}}{dp_0}\frac{dp_{q_2}}{dp_0}\Big](X)=1+\frac{\rho_n}{1-\rho_n}\,q_1q_2.$$
--
--   The two identities compute the second moment of the likelihood ratio entry by entry in Step 3 of the proof of Theorem 2.
--
--   **Formalization Note** The expectation under $p_0$ is the two-term sum over $X\in\{0,1\}$ (`Bool`), and the densities are the Bernoulli mass functions; $dp_0>0$ on both points because $\rho_n\in(0,1/2]$.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 34, Lemma 7

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Lower

/-- **Lemma 7** (Enikeeva–Klopp, p. 34). Let `ρ_n ∈ (0, 1/2]` and `q, q₁, q₂ ∈ [−1, 1]`, and let
`p₀`, `p_q` be the Bernoulli laws with parameters `ρ_n` and `ρ_n(1 + q)`. For `X ∼ p₀`,
`E₀[(dp_q/dp₀)(X)]² = 1 + ρ_n/(1 − ρ_n) q²` and
`E₀[(dp_{q₁}/dp₀)(dp_{q₂}/dp₀)](X) = 1 + ρ_n/(1 − ρ_n) q₁q₂`. The densities w.r.t. counting measure
on `{0, 1}` (`Bool`) are the Bernoulli mass functions `bern`. -/
theorem lemma_7 (ρ q q₁ q₂ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2)
    (hq : -1 ≤ q ∧ q ≤ 1) (hq₁ : -1 ≤ q₁ ∧ q₁ ≤ 1) (hq₂ : -1 ≤ q₂ ∧ q₂ ≤ 1) :
    ∑ x : Bool, bern ρ x * (bern (ρ * (1 + q)) x / bern ρ x) ^ 2 = 1 + ρ / (1 - ρ) * q ^ 2 ∧
    ∑ x : Bool, bern ρ x *
        (bern (ρ * (1 + q₁)) x / bern ρ x * (bern (ρ * (1 + q₂)) x / bern ρ x)) =
      1 + ρ / (1 - ρ) * (q₁ * q₂) := by sorry

end CPDNetworks.Lower
