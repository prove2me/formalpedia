-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
-- name    : AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/ef1ef7e4-c514-5ab5-9052-a6e9e185a346
-- title:
--   Central fold of a twisted GL₂ kernel: convergence and Fubini
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a number field, equip the idele group $(\mathbb{A}_L)^\times$ with a measurable space structure that is the Borel one, let $\nu$ be a Haar measure on $(\mathbb{A}_L)^\times$ and let $\Omega \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain for the action of the image of $L^\times$ (the range of the units map of $L \to \mathbb{A}_L$) with respect to $\nu$. Let $D$ be a datum consisting of a homomorphism from $\operatorname{Aut}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ that is continuous and compatible with principal adeles, let $\sigma : L \simeq_K L$, and write $\sigma_{\mathbb{A}}$ for the induced entrywise automorphism of $G = \mathrm{GL}_2(\mathbb{A}_L)$, $\iota$ for the entrywise embedding $\mathrm{GL}_2(L) \to G$, $c(z)$ for the central scalar matrix of an idele $z$ and $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$. Let $\xi$ be a homomorphism from the top subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function is continuous and which is trivial on principal ideles, let $A \subseteq L$ be arbitrary, and let $\varphi : G \to \mathbb{C}$ be continuous with compact support. Put $B_A = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \in A\}$, $K_A(x,y) = \sum_{\gamma \in B_A} \varphi(x^{-1}\iota(\gamma)\sigma_{\mathbb{A}}(y))$ (a finitely supported sum over $B_A$), and let $\mu_B$ be the adelic additive Haar measure, taken with the Borel structure on $\mathbb{A}_L$, conditioned on the adelic box (the infinite part lying in the preimage of the fundamental domain of the lattice basis, the finite part integral at every place); for $f$ on $G$ let $f_N(g) = \int f(n(t)g)\, d\mu_B(t)$. Then, with $G$ given its Borel structure: (i) for every $x \in G$ the function $z \mapsto \xi(z) K_A(x, c(z)x)$ is integrable on $\Omega$ for $\nu$; (ii) for every $x$ the function $z \mapsto \xi(z)\,\bigl(K_A(x,\cdot)\bigr)_N(c(z)x)$ is integrable on $\Omega$ for $\nu$; (iii) $x \mapsto \int_\Omega \xi(z) K_A(x,c(z)x)\, d\nu(z)$ is measurable; (iv) $x \mapsto \int_\Omega \xi(z)\,\bigl(K_A(x,\cdot)\bigr)_N(c(z)x)\, d\nu(z)$ is measurable; and (v) for every $x$, writing $a(x') = \int_\Omega \xi(z) K_A(x', c(z)x')\, d\nu(z)$, one has $a_N(x) = \int_\Omega \xi(z) \int \sum_{\gamma \in B_A} \varphi\bigl((n(t)x)^{-1}\iota(\gamma)\sigma_{\mathbb{A}}(n(t)c(z)x)\bigr)\, d\mu_B(t)\, d\nu(z)$, i.e. the average over the unipotent box may be interchanged with the integral over $\Omega$.
--
--   This is the convergence and interchange half of the treatment of the upper-triangular (hyperbolic) classes in the twisted trace formula for $\mathrm{GL}(2)$: it supplies integrability on a fundamental domain for the centre, Borel measurability of the resulting folded kernel and of its constant term, and the Fubini identity between the constant term of the fold and the iterated integral. It is used in the derivation of the identity comparing the fold of the constant term with the constant term of the fold under the norm condition on $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.lean

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
    AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
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
    (A : Set L)
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
          ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
              AutomorphicForm.sigmaAdelicAct K L D σ
                (AutomorphicForm.unipotentGL2 t * (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
            ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∂νZL := by sorry
