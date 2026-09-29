-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
-- name    : AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2f6571c3-cff7-5b50-8beb-f845e7830fb2
-- title:
--   Bad-place set of a non-norm idelic class in GL₂
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite and Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and suppose $[L:K]$ is prime. Let $\gamma \in GL_2(K)$ have vanishing off-diagonal entries $\gamma_{10} = \gamma_{01} = 0$ and ratio $\gamma_{00}/\gamma_{11} \neq 1$, with both $\gamma_{00}$ and $\gamma_{11}$ in the image of $\mathrm{Algebra.norm}_{K} \colon L \to K$; let $u_\gamma, d_\gamma \in K^\times$ satisfy $u_\gamma = \gamma_{00}/\gamma_{11}$ and $d_\gamma = \gamma_{11}$. Let $z$ be a unit of the adele ring of $K$ lying in the join of the image of $K^\times$ and the image of the idelic norm `idelicNorm` of `genuineBaseChange K L` (the unit-group map induced by the adelic norm of that base change datum), but not in the image of that idelic norm. Write $x = c(z\,d_\gamma)\cdot \mathrm{diag}(u_\gamma,1) \in GL_2(\mathbb{A}_K)$, where $c$ denotes the scalar embedding `centralScalar` and $\mathrm{diag}$ is `diagUnits2`. Then there is a finite set $P$ of height-one primes of $\mathcal{O}_K$ such that: for every $v \in P$ there is no $\delta \in GL_2(L \otimes_K K_v)$ with `IsNormOf K L (v.adicCompletion K) σ` applied to the $v$-component of the finite part of $x$ and $\delta$, i.e. no $y$ conjugating the image of that component in $GL_2(L \otimes_K K_v)$ to the $\sigma$-twisted norm string of $\delta$; moreover $P$ is non-empty or no such $\delta$ exists for the archimedean component $\mathrm{glArch}(x)$ over $\mathbb{A}_{K,\infty}$; and it is not the case that $|P| = 1$ while the archimedean non-existence assertion fails.
--
--   This is the bad-place bookkeeping step in the comparison of hyperbolic (split regular) terms for cyclic base change of $GL_2$: it produces, from an idele class that is globally a product of a rational and a norm but is not itself an idelic norm, a set of places at which the associated split class fails to be a $\sigma$-twisted norm, with the cardinality of that set constrained so as to exclude the single-finite-place configuration. It feeds the vanishing identity [`AutomorphicForm.finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_mem_sup_of_not_mem_range_of_prime`](thm.html#AutomorphicForm.finrank_mul_ratio_mul_weightedClassIntegral_add_mul_window_eq_zero_of_mem_sup_of_not_mem_range_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

open AutomorphicForm in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_mem_sup_of_not_mem_range_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (γ : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (hγN : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 ∈ Set.range (Algebra.norm K : L → K) ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ∈ Set.range (Algebra.norm K : L → K))
    (uγ dγ : Kˣ)
    (huγ : (uγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hdγ : (dγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (z : (AdeleRing (𝓞 K) K)ˣ)
    (hzK : z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ⊔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range)
    (hzN : z ∉ Set.range (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ v ∈ P, ¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1))) δ) ∧
      (P.Nonempty ∨
        ¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
          (AdelicLevel.glArch (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1)) δ) ∧
      ¬ (P.card = 1 ∧ ¬ (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ
          (AdelicLevel.glArch (𝓞 K) K
            (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1)) δ)) := by sorry
