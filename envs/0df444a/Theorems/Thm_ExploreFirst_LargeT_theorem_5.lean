-- Prove2me | Theorems.Thm_ExploreFirst_LargeT_theorem_5
-- name    : ExploreFirst.LargeT.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:12:17.2212+00:00
-- url     : https://prove2.me/theorems/de74211d-8216-4067-a62f-8e024d4b6c94
-- title:
--   Theorem 5, p. 17 — explicit large-horizon lower bound for each suboptimal arm
-- statement:
--   Let $\mathcal D$ be a well-behaved bandit model with witnesses $\varepsilon_{\mathcal D}$ and $\omega_{\mathcal D}$, and let $\psi$ be uniformly super-fast convergent on it with constant $C_{\psi,\mathcal D}$. For a problem $\underline\nu$ in the model and a suboptimal arm $a$, write $\mu^*$ for the largest arm mean, $\mathcal K=\mathcal K_{\inf}(\nu_a,\mu^*,\mathcal D)$, and $H(\underline\nu)=\sum_{b:\Delta_b>0}\Delta_b^{-2}$. Assume $\mu^*\in E(\mathcal D)$ and $0<\mathcal K<\infty$. For $T\ge2$ define
--   $$
--   a_T=\frac{\omega_{\mathcal D}(\nu_a,\mu^*)}{\mathcal K}(\ln T)^{-4},\quad
--   b_T=C_{\psi,\mathcal D}H(\underline\nu)\frac{\ln T}{T},\quad
--   c_T=\frac{\ln(KC_{\psi,\mathcal D}(\ln T)^9)}{\ln T}.
--   $$
--   Whenever $(\ln T)^{-4}<\varepsilon_{\mathcal D}(\mu^*)$, $a_T<1$, $b_T<1$, and $0\le c_T<1$,
--   $$
--   \mathbb E_{\underline\nu}[N_{\psi,a}(T)]\ge
--   \frac{\ln T}{\mathcal K}\bigl(1-(a_T+b_T+c_T)\bigr)-\frac{\ln2}{\mathcal K}.
--   $$
--   The theorem quantifies how many times any strategy in this class must draw each suboptimal arm, including the lower-order terms.
--
--   **Formalization Note** The witnesses and constant are fixed uniformly before the problem, arm and horizon. The paper's $\varepsilon_{\mathcal D}(\mu^*)$ requires $\mu^*\in E(\mathcal D)$, and real division requires $0<\mathcal K<\infty$. The condition $c_T\ge0$ is added because the paper's three-factor inequality requires it; $a_T,b_T\ge0$ follow from the other hypotheses. Arms use zero-based indices in Lean, and strategies are Markov kernels on observed histories.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, p. 17, Theorem 5 (18)

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting

namespace ExploreFirst.LargeT

open MeasureTheory BanditAlgorithm

/-- Theorem 5: the explicit large-horizon lower bound for each suboptimal arm. -/
theorem theorem_5 {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟)
    (εD : ℝ → ℝ) (ωD : Measure ℝ → ℝ → ℝ)
    (hwell : IsWellBehaved 𝒟 εD ωD)
    (π : BanditPolicy K) (C : ℝ)
    (hπ : IsUniformlySuperFast 𝒟 π C)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (hμ : banditOptimalMean ν ∈ expectationInterior 𝒟)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν) ≠ ⊤)
    (T : ℕ) :
    (let K₀ := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν)
     let aT := ωD (ν.P a) (banditOptimalMean ν) / K₀.toReal *
       ((Real.log T) ^ 4)⁻¹
     let bT := C * hardness ν * Real.log T / (T : ℝ)
     let cT := Real.log ((K : ℝ) * C * (Real.log T) ^ 9) / Real.log T
     2 ≤ T →
       ((Real.log T) ^ 4)⁻¹ < εD (banditOptimalMean ν) →
       aT < 1 → bT < 1 → 0 ≤ cT → cT < 1 →
       Real.log T / K₀.toReal * (1 - (aT + bT + cT)) -
         Real.log 2 / K₀.toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by sorry

end ExploreFirst.LargeT
