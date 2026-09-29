-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
-- name    : AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/ed6ee262-e634-596b-b0f6-21889160fa40
-- title:
--   Constant term of the centre-folded twisted GL₂ kernel
-- statement:
--   Let $L/K$ be a finite Galois extension of fields with $L$ a number field, and let the idele group $(\mathbb A_L)^\times$ carry a measurable structure which is the Borel structure, a Haar measure $\nu$ and a set $\Omega$ that is a fundamental domain, with respect to $\nu$, for the action of the image of $L^\times$ under `Units.map` of $\mathrm{algebraMap}$. Let $D$ be an `IdeleGaloisDescent` datum for $\mathbb A_L$ over $K$, i.e. a homomorphism $\mathrm{act}$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, each continuous, compatible with the Galois action on principal adeles; let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the group of integral powers of $\sigma$, and write $\sigma_{\mathbb A}$ for the entrywise automorphism of $\mathrm{GL}_2(\mathbb A_L)$ induced by $D.\mathrm{act}\,\sigma$. Let $\xi$ be a homomorphism from the full subgroup of $(\mathbb A_L)^\times$ to $\mathbb C^\times$ whose composite with the inclusion $\mathbb C^\times \to \mathbb C$ is continuous and which is trivial on principal ideles. Let $A \subseteq L$ satisfy $N_{L/K}(\rho) \neq 1$ for all $\rho \in A$, and let $\varphi : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ be continuous with compact support. Write $\iota$ for the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb A_L)$, $c(z)$ for the scalar matrix of an idele $z$, $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$, $B_A = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \in A\}$, $K_A(x,y) = \sum^{\mathrm f}_{\gamma \in B_A} \varphi(x^{-1}\iota(\gamma)\sigma_{\mathbb A}(y))$ (a `finsum` over $B_A$), and $f \mapsto f_N$, $f_N(g) = \int f(n(t)g)\,d\mu_B(t)$, for the constant term along the upper unipotent subgroup taken with respect to the adelic additive Haar measure conditioned on the adelic box of $L$ (infinite part in the fundamental domain of the lattice basis, finite part integral). Then: (1) for each $x$ the function $z \mapsto \xi(z)K_A(x, c(z)x)$ is integrable on $\Omega$ for $\nu$; (2) for each $x$ so is $z \mapsto \xi(z)\,(K_A(x,\cdot))_N(c(z)x)$; (3) $x \mapsto \int_\Omega \xi(z)K_A(x,c(z)x)\,d\nu$ is measurable; (4) $x \mapsto \int_\Omega \xi(z)\,(K_A(x,\cdot))_N(c(z)x)\,d\nu$ is measurable; and (5) for every $x$, the constant term at $x$ of the function $x' \mapsto \int_\Omega \xi(z)K_A(x',c(z)x')\,d\nu$ equals $\int_\Omega \xi(z)\,(K_A(x,\cdot))_N(c(z)x)\,d\nu$, the first argument of the kernel now being the fixed $x$.
--
--   This is the interchange, for the upper-triangular family $B_A$ of norm-non-unit ratio, of the constant term along the upper unipotent subgroup with the fold over the centre against the character $\xi$: the constant term of the centre-folded twisted kernel is the fold of the constant term, together with the integrability and measurability needed for both sides to make sense. It is used in the treatment of the hyperbolic contribution to the twisted trace formula, where the resulting truncated integral is shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_constantTerm_of_norm_ne_one
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (A : Set L) (hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) ∧
    ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun x' : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
            ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                φ (x'⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x')) ∂νZL)
          x =
        ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
            (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
            (fun t => AutomorphicForm.unipotentGL2 t)
            (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                  (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
            (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL := by sorry
