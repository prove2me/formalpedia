-- Prove2me | Theorems.Thm_ExploreFirst_LargeT_equation_17
-- name    : ExploreFirst.LargeT.equation_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T22:13:32.829813+00:00
-- url     : https://prove2.me/theorems/369d0c54-44a7-433d-8cba-c93616ce29e6
-- title:
--   (17), p. 17 — lower bound after super-fast convergence and optimization
-- statement:
--   Let $\psi$ be uniformly super-fast convergent on a model $\mathcal D$ with constant $C_{\psi,\mathcal D}>0$. Let $\underline\nu$ be a problem in the model, $a$ a suboptimal arm, $\varepsilon>0$, and $T\ge2$. Write $A^*_{\underline\nu}$ for the number of optimal arms, $H(\underline\nu)=\sum_{b:\Delta_b>0}\Delta_b^{-2}$, and $\mathcal K_\varepsilon=\mathcal K_{\inf}(\nu_a,\mu^*+\varepsilon,\mathcal D)$. If $0<\mathcal K_\varepsilon<\infty$ and $C_{\psi,\mathcal D}H(\underline\nu)\ln T\le T$, then
--   $$
--   \mathbb E_{\underline\nu}[N_{\psi,a}(T)]\ge
--   \frac{1-C_{\psi,\mathcal D}H(\underline\nu)\ln T/T}{\mathcal K_\varepsilon}
--   \ln\!\left(\frac{T\varepsilon^2}{A^*_{\underline\nu}C_{\psi,\mathcal D}\ln T}\right)
--   -\frac{\ln2}{\mathcal K_\varepsilon}.
--   $$
--   This is the intermediate bound to which well-behavedness is applied.
--
--   **Formalization Note** The printed claim says it holds for all $T\ge2$. The additional condition $C_{\psi,\mathcal D}H(\underline\nu)\ln T\le T$ is needed when the displayed logarithm is negative; the derivation from (15) does not cover the simultaneous opposite signs. Positivity and finiteness of $\mathcal K_\varepsilon$ make the reciprocal genuine. Theorem 5 assumes the strict version of the added horizon condition.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 16–17, (16)–(17)

import Mathlib
import Definitions.Def_ExploreFirst_LargeT_Setting

namespace ExploreFirst.LargeT

open MeasureTheory BanditAlgorithm

/-- Equation (17), in the range where its substitution from (15) is justified. -/
theorem equation_17 {K : ℕ} (𝒟 : Set (Measure ℝ))
    (h𝒟 : ExploreFirst.Asymptotic.IsModel 𝒟) (π : BanditPolicy K) (C : ℝ)
    (hπ : IsUniformlySuperFast 𝒟 π C)
    (ν : StochasticBandit K) (hν : ExploreFirst.Asymptotic.InModel 𝒟 ν)
    (a : Fin K) (ha : 0 < banditGap ν a)
    (ε : ℝ) (hε : 0 < ε)
    (hKpos : 0 < banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε))
    (hKfin : banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε) ≠ ⊤)
    (T : ℕ) (hT : 2 ≤ T) (hC : 0 < C)
    (hb : C * hardness ν * Real.log T ≤ (T : ℝ)) :
    (let Kε := banditDInf 𝒟 (ν.P a) (banditOptimalMean ν + ε)
     (1 - C * hardness ν * Real.log T / (T : ℝ)) *
       Real.log ((T : ℝ) * ε ^ 2 /
         ((ExploreFirst.Asymptotic.optimalArms ν).card * C * Real.log T)) / Kε.toReal -
       Real.log 2 / Kε.toReal ≤ ExploreFirst.FundIneq.expPulls ν π T a) := by sorry

end ExploreFirst.LargeT
