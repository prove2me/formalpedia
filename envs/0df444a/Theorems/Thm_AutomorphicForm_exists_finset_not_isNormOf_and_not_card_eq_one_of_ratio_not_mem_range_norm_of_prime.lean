-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime
-- name    : AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1558a0eb-b206-5527-9890-f10eb5c6b617
-- title:
--   Non-normic diagonal ratio: the bad place set is no singleton
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Let $\gamma \in \mathrm{GL}_2(K)$ be diagonal, in the sense that its $(1,0)$ and $(0,1)$ entries vanish, with $\gamma_{00}/\gamma_{11} \neq 1$, and let $u_\gamma, d_\gamma \in K^\times$ satisfy $u_\gamma = \gamma_{00}/\gamma_{11}$ and $d_\gamma = \gamma_{11}$; assume $u_\gamma$ is not in the image of $\mathrm{Algebra.norm}\, K : L \to K$. Let $z$ be a unit of the adele ring of $K$. Write $x$ for the element $\mathrm{diag}(z\,d_\gamma, z\,d_\gamma) \cdot \mathrm{diag}(u_\gamma, 1)$ of $\mathrm{GL}_2(\mathbb{A}_K)$, formed as the product of the scalar matrix attached to $z$ times the image of $d_\gamma$ with `diagUnits2` applied to the image of $u_\gamma$ and $1$. Then there is a finite set $P$ of height-one primes of $\mathcal{O}_K$ such that: for every $v \in P$ there is no $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ whose `normString` twisted norm is conjugate to the image of $x$ in $\mathrm{GL}_2(L \otimes_K K_v)$, i.e. `IsNormOf` fails at $v$ for the $v$-component of the finite part of $x$; moreover $P$ is nonempty or `IsNormOf` fails likewise for the image of $x$ in $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$; and it is not the case that $P$ has exactly one element while `IsNormOf` does hold over the infinite adele ring (stated as the negation of a doubly negated existential).
--
--   This is the local–global statement, resting on the Hasse norm theorem for cyclic extensions together with reciprocity, that a diagonal class whose ratio is a global non-norm is locally non-normic at a set of places which is neither empty nor a single finite place. It is used in the comparison of hyperbolic terms in the base change trace formula, where it forces the corresponding weighted class integral to contribute trivially.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime.lean

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

theorem AutomorphicForm.exists_finset_not_isNormOf_and_not_card_eq_one_of_ratio_not_mem_range_norm_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)
    (γ : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (uγ dγ : Kˣ)
    (huγ : (uγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hdγ : (dγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hγnn : (uγ : K) ∉ Set.range (Algebra.norm K : L → K))
    (z : (AdeleRing (𝓞 K) K)ˣ) :
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
