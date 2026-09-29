-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
-- name    : AutomorphicForm.integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d5db9f44-250a-5270-8552-2ac19f6b8d25
-- title:
--   Unipotent translation invariance of box averages of twisted GL₂ sums
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a number field and $L/K$ a finite Galois extension, let $D$ be an idele Galois descent datum for $L/K$, that is, a monoid homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, each continuous and each compatible with the Galois action on principal adeles, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau$ lies in the subgroup of integral powers of $\sigma$. Let $A \subseteq L$ be a set all of whose elements $\rho$ satisfy $\mathrm{N}_{L/K}(\rho) \neq 1$, let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support, and let $x, g \in \mathrm{GL}_2(\mathbb{A}_L)$. Write $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ for `unipotentGL2 t`, $\iota$ for the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$, and $\sigma_{\mathbb{A}}$ for the entrywise automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ induced by $D.\mathrm{act}\,\sigma$. All integrals are taken with respect to the additive Haar measure on $\mathbb{A}_L$ for the Borel $\sigma$-algebra of its topology, conditioned on the adelic box $B$ (the adeles whose infinite component lies in the preimage of the fundamental domain of the lattice basis of the mixed space and whose finite component is integral at every height-one prime of $\mathcal{O}_L$). Then, with the unordered sums $\sum^{\mathrm{f}}$ running over $\{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \in A\}$, the two functions $t \mapsto \sum^{\mathrm{f}}_{\gamma} \varphi\big((n(t)x)^{-1}\,\iota(\gamma)\,\sigma_{\mathbb{A}}(n(t)g)\big)$ and $t \mapsto \sum^{\mathrm{f}}_{\gamma} \varphi\big(x^{-1}\,\iota(\gamma)\,\sigma_{\mathbb{A}}(n(t)g)\big)$ are integrable for that conditioned measure, and their integrals over $\mathbb{A}_L$ coincide.
--
--   This is the substitution step showing that, for the upper-triangular classes whose diagonal ratios have norm different from $1$, translating the first variable by the same unipotent element as the second leaves the box average of the twisted $\mathrm{GL}_2$ kernel unchanged. It feeds the computation of the constant term along the upper unipotent subgroup of the corresponding part of the kernel, which cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one.lean

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

theorem
    AutomorphicForm.integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Set L) (hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Integrable (fun t : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g)))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∧
    Integrable (fun t : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g)))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∧
    ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) =
      ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) := by sorry
