-- Prove2me | Theorems.Thm_CPDNetworks_Lower_step_1
-- name    : CPDNetworks.Lower.step_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:51.105007+00:00
-- url     : https://prove2.me/theorems/1b098bf1-8b28-4b9e-abb1-21a0be96a665
-- title:
--   Proof of Theorem 2, Step 1 — the priors V₀ and V_{1,ζ}, V_{2,ζ} lie in 𝒮_n(ω_n) and 𝒲^τ_{n,T}(ω_n, R)
-- statement:
--   Let $\alpha\in(0,1)$, $\beta\in(0,1-\alpha]$, $\eta=\alpha+\beta$, $C_\eta=\log(1+4(1-\eta)^2)$, $n\ge2$ and $1\le\tau\le T-1$. Let $\omega_n$ satisfy $\omega_n>\sqrt{2C_\eta}$, $\omega_n\ge4\sqrt{2C_\eta}$ and $\omega_n\le(n-1)/2$, and put $\varepsilon_n=(2C_\eta)^{1/4}\omega_n^{-1/2}$ and $\tilde\rho_n=(1-\varepsilon_n)\omega_n/(n-1)$. Let $R>0$ with
--   $$R\sqrt T\le\varepsilon_n\omega_n .$$
--   With $\Pi=\mathbf 1_n\mathbf 1_n^{\mathsf T}$, $V_0=\tilde\rho_n(\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n)$, $\Lambda_{n,\zeta}=\frac{r_{n,\tau}}{n-1}(\zeta\zeta^{\mathsf T}-\mathrm{id}_n)$, $r_{n,\tau}=R/q(\tau/T)$, $V_{1,\zeta}=V_0-(1-\tau/T)\Lambda_{n,\zeta}$ and $V_{2,\zeta}=V_0+(\tau/T)\Lambda_{n,\zeta}$:
--   1. $(V_0,\Pi)\in\mathcal S_n(\omega_n)$;
--   2. for every $\zeta\in\{-1,+1\}^n$, $\{(V_{2,\zeta},\Pi),(V_{1,\zeta},\Pi)\}\in\mathcal W^\tau_{n,T}(\omega_n,R)$, and
--   $$q(\tau/T)\,\|\Lambda_{n,\zeta}\|_{2\to2}=R .$$
--
--   So the null prior lives on the null class and the alternative prior on the alternative class of energy $R$, which is what lets the Bayesian testing error bound the minimax one.
--
--   **Formalization Note** The page assumes only $\omega_n>\sqrt{2C_\eta}$ (that is, $\varepsilon_n\in(0,1)$). Two hypotheses are added and disclosed: $\omega_n\ge4\sqrt{2C_\eta}$, i.e. $\varepsilon_n\le1/2$, and $\omega_n\le(n-1)/2$, which gives $\tilde\rho_n\le1/2$. Without them the entries $\tilde\rho_n(1+q_{i,\tau}\zeta_i\zeta_j)$ of $V_{1,\zeta}$, $V_{2,\zeta}$ need not lie in $[0,1]$. The paper places its priors on $\tilde\Theta^t=\Pi_n\odot\Theta^t$; here $\Pi=\mathbf 1_n\mathbf 1_n^{\mathsf T}$, so $\tilde\Theta^t=\Theta^t$, which is legitimate because the type I and II errors take suprema over all sampling matrices. The paper's line "$=q(\tau/T)r_{n,\tau}\sqrt{T-1}$" is an upper bound, not an equality; only the resulting inequality is used.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, pp. 34–35, proof of Theorem 2, Step 1

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting
import Definitions.Def_CPDNetworks_Lower_Priors

namespace CPDNetworks.Lower

open scoped Matrix
open HighDimProb.RandomMatrices

/-- **Proof of Theorem 2, Step 1** (Enikeeva–Klopp, pp. 34–35): the priors are concentrated on the
classes. With `Π = 1_n1_nᵀ`, `ρ̃_n = (1 − ε_n)ω_n/(n − 1)`, `ε_n = (2C_η)^{1/4}ω_n^{−1/2}`,
`V₀ = ρ̃_n(1_n1_nᵀ − id_n)`, `Λ_{n,ζ} = r_{n,τ}/(n − 1)(ζζᵀ − id_n)`, `r_{n,τ} = R/q(τ/T)`,
`V_{1,ζ} = V₀ − (1 − τ/T)Λ_{n,ζ}` and `V_{2,ζ} = V₀ + (τ/T)Λ_{n,ζ}`: if `R√T ≤ ε_nω_n`, then
`(V₀, 1) ∈ 𝒮_n(ω_n)`, and for every sign vector `ζ`, `{(V_{2,ζ}, 1), (V_{1,ζ}, 1)} ∈ 𝒲^τ_{n,T}(ω_n, R)`
and `q(τ/T)‖Λ_{n,ζ}‖_{2→2} = R`. The hypotheses `hε` (`ε_n ≤ 1/2`) and `hωn` (`ρ̃_n ≤ 1/2`) are
disclosed additions needed for the prior's entries to lie in `[0, 1]`. -/
theorem step_1 (n T τ : ℕ) (ω α β R : ℝ) (hn : 2 ≤ n) (hτ : 1 ≤ τ) (hτT : τ < T)
    (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβα : β ≤ 1 - α)
    (hω : Real.sqrt (2 * Ceta α β) < ω) (hε : 4 * Real.sqrt (2 * Ceta α β) ≤ ω)
    (hωn : ω ≤ ((n : ℝ) - 1) / 2) (hR : 0 < R)
    (hRT : R * Real.sqrt T ≤ epsN α β ω * ω) :
    InS ω (V0 n α β ω) (onesMat n) ∧
      ∀ b : Fin n → Bool,
        InW T τ ω R (V2 n T τ α β ω R b) (V1 n T τ α β ω R b) (onesMat n) ∧
          q ((τ : ℝ) / T) * matrixOpNorm (Lam n T τ R b) = R := by sorry

end CPDNetworks.Lower
