-- Prove2me | Theorems.Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
-- name    : AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/2b5a4069-775a-502f-90c8-51e930231423
-- title:
--   Slope comparison of hyperbolic class sums under base change
-- statement:
--   Fix number fields $K \subseteq L$, Haar measures $\nu_{Z}^{L}$ on $(\mathbb{A}_L)^{\times}$ and $\nu_{Z}^{K}$ on $(\mathbb{A}_K)^{\times}$ (with Borel measurable structures), and write $N$ for the idelic norm of the base change `genuineBaseChange K L`, i.e. the map on unit groups induced by the $\mathbb{A}_K$-algebra norm of $\mathbb{A}_L$. Let $N^1 \le (\mathbb{A}_L)^{\times}$ be a closed subgroup whose elements are exactly the $z$ with $N z = 1$, with a Haar measure $\mu_{N}$, and let $\mathrm{HaarQuotient.measure}$ denote the push-forward to the orbit quotient of $\nu_Z^L$ weighted by the density of $N^1$ for $\mu_N$. Assume $C>0$ satisfies, for measurable $g$ with values in $\mathbb{R}_{\ge 0}^{\infty}$ resp. $\mathbb{C}$, the comparison $\int_{(\mathbb{A}_L)^{\times}/N^1} g(N(\mathrm{wq.out})) = C \int_{\mathrm{range}\,N} g \, d\nu_Z^K$, together with the corresponding integrability equivalence. Let $\xi_L \colon (\mathbb{A}_L)^{\times} \to \mathbb{C}^{\times}$ be a continuous character (as a homomorphism from the top subgroup) and $\Xi$ the nonempty finite set of those characters $\xi$ of $(\mathbb{A}_K)^{\times}$ that are continuous, trivial on the image of $K^{\times}$, and satisfy $\xi \circ N = \xi_L$. Let $\Delta_\varphi \subseteq \mathrm{GL}_2(L)$, $\Delta_K \subseteq \mathrm{GL}_2(K)$ be finite, and $n$ a map sending $\Delta_\varphi$ into $\Delta_K$, injective on $\Delta_\varphi$, with $(n t)_{00}/(n t)_{11} = \mathrm{N}_{L/K}(t_{00}/t_{11})$. Let $I_L, I_K$ be families of complex functions on the respective idele groups such that each $I_K(\gamma)$, $\gamma \in \Delta_K$, is measurable, vanishes off $\mathrm{range}\,N$, and has $\xi \cdot I_K(\gamma)$ integrable for $\xi \in \Xi$; assume $I_L(t,w) = c_0' \, I_K(n t, N w)$ for $t \in \Delta_\varphi$ and all $w$, with $c_0' \ge 0$, and that $\sum_{\xi \in \Xi} \int \xi \, I_K(\gamma) \, d\nu_Z^K = 0$ for every $\gamma \in \Delta_K$ outside $n(\Delta_\varphi)$. Finally let $\kappa_0^L, \kappa^L, \kappa_0^K, \kappa^K$ be reals with $\kappa_0^K, \kappa^K > 0$. Then $$\sum_{t \in \Delta_\varphi} 2\kappa_0^L \varepsilon_t \,\kappa^L \!\int_{(\mathbb{A}_L)^{\times}/N^1} \xi_L \, I_L(t) = \frac{\kappa_0^L \kappa^L C c_0'}{\kappa_0^K \kappa^K |\Xi|} \sum_{\xi \in \Xi} \sum_{\gamma \in \Delta_K} 2\kappa_0^K \varepsilon_\gamma \, \kappa^K \!\int_{(\mathbb{A}_K)^{\times}} \xi \, I_K(\gamma),$$ where $\varepsilon_t = 1/2$ if $\mathrm{N}_{L/K}(t_{00}/t_{11}) = -1$ and $1$ otherwise, and $\varepsilon_\gamma = 1/2$ if $\gamma_{00}/\gamma_{11} = -1$ and $1$ otherwise, the integrals over the quotient being taken against $\mathrm{HaarQuotient.measure}\ \nu_Z^L\ N^1\ \mu_N$ and evaluated at chosen representatives.
--
--   This is the bookkeeping step in the comparison of the hyperbolic contributions to the trace formulae for $\mathrm{GL}_2$ over $L$ and over $K$ under base change: the per-class matching of the class integrals, the orthogonality count over the finite fibre $\Xi$ of characters above $\xi_L$, and the measure-comparison constant $C$ are combined into the single displayed slope factor $\kappa_0^L \kappa^L C c_0' / (\kappa_0^K \kappa^K |\Xi|)$. It is used by the two statements that assemble the hyperbolic slope comparison for affine winding data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm.lean

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

theorem AutomorphicForm.sum_mul_integral_haarQuotient_ker_idelicNorm_eq_slopeFactor_mul_sum_sum_mul_integral_of_forall_eq_mul_comp_idelicNorm
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

    (IL : GL (Fin 2) L → (AdeleRing (𝓞 L) L)ˣ → ℂ) (IK : GL (Fin 2) K → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIKm : ∀ γ ∈ ΔK, Measurable (IK γ))
    (hIKi : ∀ γ ∈ ΔK, ∀ ξ ∈ Ξ,
      Integrable (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z) νZK)
    (hIK0 : ∀ γ ∈ ΔK, ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm → IK γ z = 0)

    (c₀' : NNReal)
    (hmatch : ∀ t ∈ Δφ, ∀ w : (AdeleRing (𝓞 L) L)ˣ, IL t w = (c₀' : ℂ) * IK (n t) ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w))
    (hvan : ∀ γ ∈ ΔK, (∀ t ∈ Δφ, n t ≠ γ) →
      ∑ ξ ∈ Ξ, ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK = 0)

    (κ₀L κL κ₀K κK : ℝ) (hκ₀K : 0 < κ₀K) (hκK : 0 < κK) :
    ∑ t ∈ Δφ, 2 * ((κ₀L : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
            then (1 / 2 : ℂ) else 1)) *
        (((κL : ℝ) : ℂ) * ∫ wq : MulAction.orbitRel.Quotient N1 (AdeleRing (𝓞 L) L)ˣ,
              ((ξL ⟨(wq.out : (AdeleRing (𝓞 L) L)ˣ), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * IL t wq.out ∂(HaarQuotient.measure νZL N1 μN)) =
      (((κ₀L : ℂ) * (κL : ℂ) * (C : ℂ) * (c₀' : ℂ)) / ((κ₀K : ℂ) * (κK : ℂ) * (Ξ.card : ℂ))) *
        ∑ ξ ∈ Ξ, ∑ γ ∈ ΔK, 2 * ((κ₀K : ℂ) * (if (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = -1 then (1 / 2 : ℂ) else 1)) *
          (((κK : ℝ) : ℂ) * ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK γ z ∂νZK) := by sorry
