-- Prove2me | Theorems.Thm_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
-- name    : AutomorphicForm.exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/12b8daa4-9feb-54cd-aeba-c73cda3606f2
-- title:
--   Idelic base change for a cyclic extension: fixed idèles form the image
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra and $L/K$ Galois, and let $D$ be an idèle Galois descent datum for $L/K$: a monoid homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adèle ring $\mathbb{A}_L$ of $L$, such that each $D.\mathrm{act}\,\tau$ is continuous and restricts along the structure map $L \to \mathbb{A}_L$ to $\tau$ on $L$. Let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. The conclusion asserts the existence of a monoid homomorphism $\theta \colon \mathbb{A}_K^{\times} \to \mathbb{A}_L^{\times}$ which is continuous and injective and satisfies three further properties: for every $a$, the idèle norm of $\theta(a)$, defined as the real value of the distinguished Haar character of $\mathbb{A}_L$ at $\theta(a)$, equals the corresponding norm of $a$ over $K$ raised to the power $\operatorname{finrank}_K L$; for every $k \in K^{\times}$, $\theta$ sends the principal idèle of $k$ in $\mathbb{A}_K^{\times}$ to the principal idèle in $\mathbb{A}_L^{\times}$ of the image of $k$ in $L$; and for every $b \in \mathbb{A}_L^{\times}$, the induced automorphism $D.\mathrm{unitsAct}\,\sigma$ of $\mathbb{A}_L^{\times}$ fixes $b$ if and only if $b$ lies in the range of $\theta$.
--
--   This is the idelic base change map $\mathbb{A}_K^{\times} \to \mathbb{A}_L^{\times}$ for a cyclic extension, packaged as an abstract $\theta$ together with the four properties — continuity, injectivity, multiplicativity of the norm with exponent $[L:K]$, compatibility with principal idèles, and identification of its image with the $\sigma$-fixed idèles — relative to a descent datum for the Galois action on $\mathbb{A}_L$. It feeds the computations of the hyperbolic contributions in the twisted trace formula, where the fundamental-domain and integral identities are stated in terms of such a $\theta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_idelesBaseChange_continuous_injective_norm_pow_range_eq_fixed
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    ∃ θ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 L) L)ˣ, Continuous θ ∧ Function.Injective θ ∧
      (∀ a, NumberField.TateGlobal.ideleNorm L (θ a) = NumberField.TateGlobal.ideleNorm K a ^ Module.finrank K L) ∧
      (∀ k : Kˣ, θ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k) =
        Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (algebraMap K L : K →* L) k)) ∧
      (∀ b : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ b = b ↔ b ∈ Set.range θ) := by sorry
