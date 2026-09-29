-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
-- name    : AutomorphicForm.integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9a75ca99-0839-5502-aeb7-a4af179cb332
-- title:
--   Unfolding a partial twisted class sum against the idele centre
-- statement:
--   Let $K$ be a field and $L$ a number field with a $K$-algebra structure, and write $\mathbb{A}_L$ for the adele ring of $L$ (relative to $\mathcal{O}_L$), $\iota\colon \mathrm{GL}_2(L)\to \mathrm{GL}_2(\mathbb{A}_L)$ for the entrywise map induced by $L\to\mathbb{A}_L$, and $c(z)=\mathrm{diag}(z,z)$ for the central scalar attached to $z\in\mathbb{A}_L^{\times}$. Assume $\mathbb{A}_L^{\times}$ carries a Borel measurable structure, let $\nu$ be a Haar measure on it, and let $\Omega\subseteq\mathbb{A}_L^{\times}$ be a fundamental domain for the action of the image of $L^{\times}$ in $\mathbb{A}_L^{\times}$ with respect to $\nu$. Let $D$ be an idelic Galois descent datum for $\mathcal{O}_L$, $K$, $L$, namely a homomorphism $\mathrm{Aut}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ whose value at each $g$ is continuous and extends $g$ along $L\to\mathbb{A}_L$; let $\sigma\in\mathrm{Aut}(L/K)$ and write $\sigma_{\mathbb{A}}$ for the entrywise automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D(\sigma)$, and $\sigma$ also for the entrywise automorphism of $\mathrm{GL}_2(L)$. Let $\xi$ be a homomorphism from the full subgroup $\top$ of $\mathbb{A}_L^{\times}$ to $\mathbb{C}^{\times}$ such that $z\mapsto\xi(z)$ is continuous as a complex-valued function and $\xi$ is trivial on the image of $L^{\times}$. Fix $\delta_0\in\mathrm{GL}_2(L)$ and a subgroup $\Lambda\le\mathrm{GL}_2(L)$ characterised by $\gamma\in\Lambda \iff \delta_0^{-1}\gamma\delta_0\sigma(\gamma)^{-1}\in Z(\mathrm{GL}_2(L))$, a family $r\colon\iota\to\mathrm{GL}_2(L)$ such that every $\gamma$ satisfies $r_i^{-1}\gamma\in\Lambda$ for exactly one index $i$, and an arbitrary subset $S$ of the index type. Let $\varphi\colon\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ be continuous with compact support and $x\in\mathrm{GL}_2(\mathbb{A}_L)$. Put $y_i=\iota(r_i)^{-1}x$ and $F_i(z)=\xi(z)\,\varphi\bigl(y_i^{-1}\,\iota(\delta_0)\,\sigma_{\mathbb{A}}(c(z)y_i)\bigr)$, and let $I_S=\{\delta\in\mathrm{GL}_2(L):\exists i\in S,\ \delta_0^{-1}r_i^{-1}\delta\,\sigma(r_i)\in Z(\mathrm{GL}_2(L))\}$. The assertion is fourfold: the set of indices $i$ for which $\varphi\bigl(y_i^{-1}\iota(\delta_0)\sigma_{\mathbb{A}}(c(z)y_i)\bigr)\neq 0$ for some $z$ is finite; each $F_i$ is $\nu$-integrable on $\mathbb{A}_L^{\times}$; the function $z\mapsto \xi(z)\sum^{\mathrm{f}}_{\delta\in I_S}\varphi\bigl(x^{-1}\iota(\delta)\sigma_{\mathbb{A}}(c(z)x)\bigr)$, the inner sum being a finite-support sum over $I_S$, is integrable on $\Omega$; and its integral over $\Omega$ equals $\sum_{i\in S}\int_{\mathbb{A}_L^{\times}}F_i\,d\nu$, the outer sum being a $\mathbb{C}$-valued series indexed by the subtype $S$.
--
--   This is the unfolding step for a single twisted conjugacy class in the kernel of the trace formula, here in the sub-family form in which only the cosets indexed by $S$ are retained: folding the integral over a fundamental domain of the idele class group turns the partial sum over the centre-saturated $\sigma$-twisted class of $\delta_0$ into a sum of twisted orbital integrands over the chosen coset representatives. It feeds the subsequent assembly of indicator and Weyl-element contributions to the geometric side, and the finiteness assertions rest on discreteness of the principal points in the adeles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory

theorem AutomorphicForm.integrableOn_and_setIntegral_mul_finsum_sigmaConjClassOrbit_cosetFamily_eq_tsum_subtype_integral
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (S : Set ι)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    {i : ι | ∃ z : (AdeleRing (𝓞 L) L)ˣ,
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ≠
          0}.Finite ∧
    (∀ i : ι, Integrable (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))))
        νZL) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
            δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈
              Subgroup.center (GL (Fin 2) L)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
    (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ i ∈ S,
            δ₀⁻¹ * ((r i)⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) (r i)) ∈
              Subgroup.center (GL (Fin 2) L)},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) =
      ∑' i : S, ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        φ (((AutomorphicForm.globalPoints (𝓞 L) L (r (i : ι)))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ
            (AutomorphicForm.centralScalar (𝓞 L) L z *
              ((AutomorphicForm.globalPoints (𝓞 L) L (r (i : ι)))⁻¹ * x))) ∂νZL := by sorry
