-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
-- name    : AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/028bf699-ac62-5083-8cc7-392817fc7495
-- title:
--   Archimedean twisted fibration over the norm-one torus
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and suppose $[L:K]$ is prime. Write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$, let $\sigma_E$ be the ring endomorphism $\sigma \otimes \mathrm{id}$ of $E$ ([`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199)), let $\iota : \mathbb{A}_{K,\infty}^\times \to E^\times$ be induced by $p \mapsto 1 \otimes p$, and let $U$ be the kernel of the map on units induced by the norm $\mathrm{Algebra.norm} : E \to \mathbb{A}_{K,\infty}$. Given Haar measures $\rho$ on $\mathbb{A}_{K,\infty}^\times$, $\rho_E$ on $E^\times$ and $\theta$ on $U$ (each group carrying its Borel $\sigma$-algebra), the assertion is that there exists a real $c > 0$ with two properties. First, for every measurable $\Theta : E^\times \to [0,\infty]$ and measurable $G : U \to [0,\infty]$ such that $\int \Theta(s\,\iota(p))\,d\rho(p) = G(v)$ whenever $s \in E^\times$ and $v \in U$ satisfy $v = s^{-1}\sigma_E(s)$, one has $\int_{E^\times} \Theta\, d\rho_E = c \int_U G\, d\theta$ in $[0,\infty]$. Second, for every $g : E^\times \to \mathbb{C}$ integrable for $\rho_E$ and every $\theta$-a.e. strongly measurable $G : U \to \mathbb{C}$ satisfying the same fibre identity with Bochner integrals, $G$ is $\theta$-integrable and $\int_{E^\times} g\, d\rho_E = c \int_U G\, d\theta$.
--
--   This is the archimedean unfolding step for twisted orbital integrals on a cyclic extension of prime degree: the fibres of $s \mapsto s^{-1}\sigma_E(s)$ are the cosets of $\iota(\mathbb{A}_{K,\infty}^\times) = (E^\times)^{\sigma_E}$, the map is onto the norm-one subgroup by Hilbert's Satz 90, and Weil's quotient-measure formula converts an integral over $E^\times$ into one over the norm-one torus up to a positive constant depending only on the chosen Haar measures. It is used in the evaluation of twisted orbital integrals at diagonal torus elements in the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped ENNReal in

theorem AutomorphicForm.exists_pos_forall_lintegral_units_tensor_eq_mul_lintegral_ker_norm_of_forall_lintegral_mul_includeRight_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρE : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρE.IsHaarMeasure]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      (∀ (Θ : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℝ≥0∞), Measurable Θ →
        ∀ (G : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℝ≥0∞), Measurable G →
          (∀ (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
              ((v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s →
              ∫⁻ p, Θ (s * Units.map
                  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p) ∂ρ =
                G v) →
          ∫⁻ s, Θ s ∂ρE = ENNReal.ofReal c * ∫⁻ v, G v ∂θ) ∧
      (∀ (g : (L ⊗[K] InfiniteAdeleRing K)ˣ → ℂ), Integrable g ρE →
        ∀ (G : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker → ℂ), AEStronglyMeasurable G θ →
          (∀ (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) (v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker),
              ((v : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) : (L ⊗[K] InfiniteAdeleRing K)ˣ) = s⁻¹ * Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s →
              ∫ p, g (s * Units.map
                  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom) p) ∂ρ =
                G v) →
          Integrable G θ ∧ ∫ s, g s ∂ρE = (c : ℂ) * ∫ v, G v ∂θ) := by sorry
