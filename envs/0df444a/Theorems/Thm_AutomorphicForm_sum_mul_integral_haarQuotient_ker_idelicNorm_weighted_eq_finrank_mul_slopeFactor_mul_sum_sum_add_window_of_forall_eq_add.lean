-- Prove2me | Theorems.Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
-- name    : AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/2e476a4a-f817-5582-85b8-3f6f2a3930c4
-- title:
--   Weighted intercept comparison for base change on GL(2)
-- statement:
--   Let $K \subseteq L$ be number fields, and let $\nu_{Z,L}$, $\nu_{Z,K}$ be Haar measures on the idele unit groups $(\mathbb{A}_L)^\times$, $(\mathbb{A}_K)^\times$. Let $N_1$ be a closed subgroup of $(\mathbb{A}_L)^\times$ consisting exactly of the $z$ with $\mathcal{N}(z)=1$, where $\mathcal{N}$ is the idelic norm attached to [`M4aHerbrand.GenuineDescent.genuineBaseChange`](def/M4aHerbrand_GenuineDescent.html#L87), i.e. the unit map of the algebra norm $\mathbb{A}_L \to \mathbb{A}_K$ for the base-change ring map, and let $\mu_N$ be Haar on $N_1$. The quotient measure [`HaarQuotient.measure νZL N1 μN`](def/HaarQuotient.html#L28) is the pushforward to the orbit quotient of $\nu_{Z,L}$ weighted by [`HaarQuotient.density`](def/HaarQuotient.html#L25). Assume a constant $C>0$ such that, for measurable $g$ on $(\mathbb{A}_K)^\times$, integration over the quotient of $g(\mathcal{N}(\cdot))$ equals $C$ times the integral of $g$ over $\operatorname{range}\mathcal{N}$ with respect to $\nu_{Z,K}$, both in the $[0,\infty]$-valued and the complex case, the latter together with the equivalence of the two integrability conditions. Let $\xi_L$ be a character of $(\mathbb{A}_L)^\times$ (a monoid homomorphism from the top subgroup to $\mathbb{C}^\times$) with continuous scalar realisation, and let $\Xi$ be the finite set, assumed nonempty, of characters $\xi$ of $(\mathbb{A}_K)^\times$ that are continuous, trivial on principal ideles, and satisfy $\xi \circ \mathcal{N} = \xi_L$. Let $\Delta_\varphi \subseteq \mathrm{GL}_2(L)$ and $\Delta_K \subseteq \mathrm{GL}_2(K)$ be finite sets and $n$ a map sending $\Delta_\varphi$ injectively into $\Delta_K$ with $(n t)_{00}/(n t)_{11} = \mathrm{N}_{L/K}(t_{00}/t_{11})$. Let $J_L$, $J_K$, $\mathrm{Win}$ be complex-valued kernels, with $\xi_L J_L(t,\cdot)$ integrable on the quotient for $t \in \Delta_\varphi$, each $J_K(\gamma,\cdot)$ measurable and each $\xi J_K(\gamma,\cdot)$ integrable for $\gamma \in \Delta_K$, $\xi \in \Xi$, and $J_K(\gamma,z)=0$ for $z \notin \operatorname{range}\mathcal{N}$. Let $c_G,c_T,c_G',c_T'>0$, let $c_0' \ge 0$ with $(c_G' c_T)/(c_G c_T') = c_0'$, and assume the pointwise identity $J_L(t,w) = [L:K]\,(c_G'c_T)/(c_Gc_T')\,J_K(n t, \mathcal{N}w) + c_G'c_T'^{-1}\mathrm{Win}(t,w)$ for $t \in \Delta_\varphi$, together with the vanishing of $\sum_{\xi \in \Xi}\int \xi\, J_K(\gamma,\cdot)\,d\nu_{Z,K}$ for every $\gamma \in \Delta_K$ outside the image of $n$. Finally let $\kappa_0^L,\kappa^L,\kappa_0^K,\kappa^K$ be real with $\kappa_0^K,\kappa^K>0$. Then the weighted $L$-side sum $\sum_{t \in \Delta_\varphi} \kappa_0^L \varepsilon_t\,\kappa^L \int \xi_L J_L(t,\cdot)$, where $\varepsilon_t = 1/2$ if $\mathrm{N}_{L/K}(t_{00}/t_{11}) = -1$ and $1$ otherwise, equals $[L:K]\,\bigl(\kappa_0^L\kappa^L C c_0'\bigr)/\bigl(\kappa_0^K\kappa^K |\Xi|\bigr)$ times $\sum_{\xi \in \Xi}\sum_{\gamma \in \Delta_K} \kappa_0^K \varepsilon_\gamma\,\kappa^K \int \xi J_K(\gamma,\cdot)\,d\nu_{Z,K}$, with $\varepsilon_\gamma = 1/2$ if $\gamma_{00}/\gamma_{11} = -1$ and $1$ otherwise, plus $c_G'c_T'^{-1}$ times the same weighted $L$-side sum formed with $\mathrm{Win}$ in place of $J_L$.
--
--   This is the weighted (intercept) half of the hyperbolic term comparison in cyclic base change for $\mathrm{GL}(2)$: the weighted class sums on $L$ are expressed as an explicit multiple of the corresponding sums on $K$, summed over the characters of $(\mathbb{A}_K)^\times$ pulling back to $\xi_L$, plus the window contribution. It rests on the norm-kernel quotient integration formula and feeds the statement extracting the hyperbolic intercept and matching constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add.lean

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_HaarQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal

open scoped Classical in

theorem AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_weighted_eq_finrank_mul_slopeFactor_mul_sum_sum_add_window_of_forall_eq_add
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νZK.IsHaarMeasure]
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]

    (C : ℝ) (hC : 0 < C)
    (hCl : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ENNReal, Measurable g →
        ∫⁻ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          ENNReal.ofReal C *
            ∫⁻ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (hCi : ∀ g : (AdeleRing (𝓞 K) K)ˣ → ℂ, Measurable g →
        (Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ)))
            (HaarQuotient.measure νZL N1 μN) ↔
          IntegrableOn g (Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) νZK) ∧
        ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
            g ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm (wq.out : (AdeleRing (𝓞 L) L)ˣ))
            ∂(HaarQuotient.measure νZL N1 μN) =
          C * ∫ u in Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm, g u ∂νZK)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩))
    (hΞne : Ξ.Nonempty)

    (Δφ : Finset (GL (Fin 2) L)) (ΔK : Finset (GL (Fin 2) K))
    (n : GL (Fin 2) L → GL (Fin 2) K) (hn : ∀ t ∈ Δφ, n t ∈ ΔK)
    (hninj : ∀ t ∈ Δφ, ∀ t' ∈ Δφ, n t = n t' → t = t')
    (hnr : ∀ t ∈ Δφ, ((n t : Matrix (Fin 2) (Fin 2) K) 0 0 / (n t : Matrix (Fin 2) (Fin 2) K) 1 1) =
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1))

    (JL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ) (JK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (Win : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ)
    (hJLi : ∀ t ∈ Δφ, Integrable (fun wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out)
      (HaarQuotient.measure νZL N1 μN))
    (hJKm : ∀ γ ∈ ΔK, Measurable (JK γ))
    (hJKi : ∀ γ ∈ ΔK, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z) νZK)
    (hJK0 : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → JK γ z = 0)

    (cG cT cG' cT' : ℝ) (hcG : 0 < cG) (hcT : 0 < cT) (hcG' : 0 < cG') (hcT' : 0 < cT')
    (c₀' : NNReal) (hρ : (cG' * cT) / (cG * cT') = (c₀' : ℝ))
    (hwin : ∀ t ∈ Δφ, ∀ w : (AdeleRing (𝓞 L) L)ˣ,
      JL t w = (Module.finrank K L : ℂ) * (((cG' * cT) / (cG * cT') : ℝ) : ℂ) * JK (n t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w) +
        ((cG' * cT'⁻¹ : ℝ) : ℂ) * Win t w)
    (hvan : ∀ γ ∈ ΔK, (∀ t ∈ Δφ, n t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK = 0)

    (κ₀L κL κ₀K κK : ℝ) (hκ₀K : 0 < κ₀K) (hκK : 0 < κK) :
    ∑ t ∈ Δφ, ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
        (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * JL t wq.out ∂(HaarQuotient.measure νZL N1 μN)) =
      (Module.finrank K L : ℂ) * (((κ₀L : ℂ) * (κL : ℂ) * (C : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * (κK : ℂ) * (Ξ.card : ℂ))) *
        ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * JK γ z ∂νZK) +
      ((cG' * cT'⁻¹ : ℝ) : ℂ) *
        ∑ t ∈ Δφ, ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
          (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * Win t wq.out ∂(HaarQuotient.measure νZL N1 μN)) := by sorry
