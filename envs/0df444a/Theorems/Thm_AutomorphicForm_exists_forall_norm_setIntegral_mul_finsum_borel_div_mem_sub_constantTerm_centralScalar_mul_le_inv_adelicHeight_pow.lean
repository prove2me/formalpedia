-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
-- name    : AutomorphicForm.exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/1e2110f2-ada2-52cb-ac29-955526887abf
-- title:
--   Rapid decay of the ξ-averaged twisted kernel minus its constant term
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and a $K$-algebra, and equip the idele group $(\mathbb{A}_L)^\times$ with a measurable structure that is the Borel structure and a Haar measure $\nu_{Z,L}$. Let $\Omega_L \subseteq (\mathbb{A}_L)^\times$ be a fundamental domain, for $\nu_{Z,L}$, of the subgroup of principal ideles, i.e. the range of the map induced on units by $L \to \mathbb{A}_L$. Let $D$ be an idele Galois descent datum for $L/K$: a monoid homomorphism from $L \simeq_{\text{alg}[K]} L$ to the ring automorphisms of $\mathbb{A}_L$, each continuous, compatible with the Galois action on principal adeles; let $\sigma$ be a $K$-automorphism of $L$, and write $\sigma_{\mathbb{A}}$ for the entrywise action of $D(\sigma)$ on $\mathrm{GL}_2(\mathbb{A}_L)$. Let $\xi_L$ be a homomorphism from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function is continuous and which is trivial on principal ideles. Let $c, u, d_1, d_2$ be reals with $c > 0$, let $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ be compact, and let $S$ be contained in the union of the right translates $\mathfrak{S}y$, $y \in T_c$, of the centre-cut Siegel set $\mathfrak{S} = \mathfrak{S}(c,u,d_1,d_2)$ consisting of those $g$ whose finite part lies in the finite integral $\mathrm{GL}_2$, whose archimedean component has local height $\ge c$ and window quantity $\mathrm{xWindowSq} \le u^2$ at every infinite place, and whose archimedean determinant norm lies in $[d_1,d_2]$ at every infinite place. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be a factorizable test function, i.e. a product $\varphi(g) = \varphi_\infty(g_\infty)\varphi_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $\varphi_\infty$ of compact support and given by a $C^\infty$ function of the archimedean matrix entries in the mixed space, and $\varphi_{\mathrm{fin}}$ locally constant of compact support. Then there is a threshold $T_1 \in \mathbb{R}$ such that for every $N \in \mathbb{N}$ there is $C \in \mathbb{R}$ with the following property: for every subset $A \subseteq L$ and every $x \in S$ with $\mathrm{adelicHeight}_L(x) > T_1$, writing $B_A = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \in A\}$ and $K_A(x,y) = \sum_{\gamma \in B_A} \varphi(x^{-1}\,\gamma_{\mathbb{A}}\,\sigma_{\mathbb{A}}(y))$ (a finite-support sum, with $\gamma_{\mathbb{A}}$ the image of $\gamma$ in $\mathrm{GL}_2(\mathbb{A}_L)$), one has $$\Bigl\|\int_{\Omega_L} \xi_L(z)\Bigl(K_A\bigl(x, z\cdot x\bigr) - \int K_A\bigl(x, n(t)\, z \cdot x\bigr)\,d\mu_{\mathrm{box}}(t)\Bigr)\,d\nu_{Z,L}(z)\Bigr\| \le C\,\bigl(\mathrm{adelicHeight}_L(x)\bigr)^{-N},$$ where $z \cdot x$ denotes the product of the central scalar matrix with entry $z$ and $x$, $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$, and $\mu_{\mathrm{box}}$ is the additive adelic Haar measure on $\mathbb{A}_L$ (for the Borel structure) conditioned on the adelic box of points whose infinite part lies in the infinite box and whose finite part is an integral finite adele; the adelic height of $x$ is the product of the archimedean and finite heights of its two components.
--
--   This is the rapid-decay (cusp) estimate for the upper-triangular part of the geometric side of a twisted trace formula on $\mathrm{GL}_2$, in the form where the centre has already been integrated out over a fundamental domain for the principal ideles against an idele class character: high in a centre-cut Siegel set the kernel minus its constant term along the upper unipotent subgroup decays faster than any power of the adelic height, uniformly in the parameter set $A \subseteq L$. It is the boundedness input to the subsequent statement that the corresponding truncated integrals are integrable and, in the relevant range, vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

theorem
    AutomorphicForm.exists_forall_norm_setIntegral_mul_finsum_borel_div_mem_sub_constantTerm_centralScalar_mul_le_inv_adelicHeight_pow
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (S : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hS : S ⊆ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφf : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ T₁ : ℝ, ∀ N : ℕ, ∃ C : ℝ, ∀ A : Set L,
      ∀ x ∈ S, T₁ < NumberField.AdelicHeight.adelicHeight L x →
        ‖∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                  (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
            - @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
                (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                    (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL‖ ≤
          C * (NumberField.AdelicHeight.adelicHeight L x)⁻¹ ^ N := by sorry
