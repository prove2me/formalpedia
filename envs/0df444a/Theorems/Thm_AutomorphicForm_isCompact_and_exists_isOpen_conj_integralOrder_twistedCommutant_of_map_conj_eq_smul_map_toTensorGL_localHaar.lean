-- Prove2me | Theorems.Thm_AutomorphicForm_isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- name    : AutomorphicForm.isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/69c3d430-fa96-5d54-9698-8f38e1efad15
-- title:
--   Compact, relatively open conjugated integral twisted commutant
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra of degree $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-algebra automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and let $v$ be a height-one prime of $\mathcal{O}_K$, with completion $K_v$ and valuation ring $\mathcal{O}_v$. Fix $\delta \in \mathrm{GL}_2(L \otimes_K K_v)$ and a Haar measure $\tau'$ (for the Borel structure) on the twisted centralizer $\{t \mid t\,\delta\,(\sigma_{\mathrm{GL}}t)^{-1} = \delta\}$, where $\sigma_{\mathrm{GL}}$ acts entrywise by $\sigma \otimes \mathrm{id}$; fix $y \in \mathrm{GL}_2(L \otimes_K K_v)$ and $t_v \in [0,\infty]$, and assume that the push-forward of $\tau'$ along $t \mapsto y^{-1} t y$ equals $t_v$ times the push-forward, along the map induced by $a \mapsto 1 \otimes a$, of the Haar measure on $\mathrm{GL}_2(K_v)$ normalised by the compact set of integral matrices. Let $D = \{x \in M_2(L \otimes_K K_v) \mid x\delta = \delta\,(\sigma\otimes\mathrm{id})(x)\}$ and suppose $\Lambda$ equals the intersection of $D$ with the set of $x$ such that $y^{-1} x y = 1 \otimes m$ entrywise for some $m \in M_2(\mathcal{O}_v)$. Then $\Lambda$ is compact; $\Lambda = V \cap D$ for some open $V \subseteq M_2(L \otimes_K K_v)$; and an invertible $x$ has its matrix in $\Lambda$ if and only if that matrix lies in $D$ and $y^{-1} x y$ is the image of some $g \in \mathrm{GL}_2(K_v)$ with all entries in $\mathcal{O}_v$ under $\mathrm{GL}_2(K_v) \to \mathrm{GL}_2(L \otimes_K K_v)$.
--
--   This is the local topological input at a place $v$ treated by conjugation by $y$: the conjugated integral order inside the twisted commutant of $\delta$ is compact and relatively open in that commutant, with an explicit description of its invertible elements. It is used in the choice of level, in [`AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_finset_level_isOpen_isCompact_box_subset_indicator_mulVec_eq_prod_indicator_tensorPlace_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two), where the corresponding local sets must be compact open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal NNReal Topology

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.isCompact_and_exists_isOpen_conj_integralOrder_twistedCommutant_of_map_conj_eq_smul_map_toTensorGL_localHaar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (hτ'h : τ'.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (tv : ℝ≥0∞)
    (hτ' : (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τ' =
          tv • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)))
    (Λ : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hΛ : Λ = {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∩
      {x | ∃ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, m i j ∈ v.adicCompletionIntegers K) ∧
        ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * x *
          ((y : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
          m.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K)}) :
    IsCompact Λ ∧
    (∃ V : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)), IsOpen V ∧ Λ = V ∩ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)}) ∧
    (∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
      (x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ Λ ↔
        ((x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ {x | x * ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) =
            ((δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
              x.map (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ)} ∧
          ∃ g : GL (Fin 2) (v.adicCompletion K),
            (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
            y⁻¹ * x * y = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g)) := by sorry
