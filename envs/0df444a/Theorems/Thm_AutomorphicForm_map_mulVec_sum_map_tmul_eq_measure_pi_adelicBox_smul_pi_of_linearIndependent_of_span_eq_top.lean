-- Prove2me | Theorems.Thm_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
-- name    : AutomorphicForm.map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/6c966379-95b9-55ef-ab09-c6d89fb572c8
-- title:
--   Adelic Haar pushforward along base change of a K-basis
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\iota$ be a finite index type, let $b : \iota \to M_2(L)$ be a family of $2\times 2$ matrices over $L$ and let $v \in L^2$. Assume that the family $i \mapsto b_i v$ of vectors in $L^2$ is linearly independent over $K$ and spans $L^2$ over $K$, i.e. is a $K$-basis of $L^2$. Fix Borel measurable structures on the adele rings $\mathbb{A}_K$ and $\mathbb{A}_L$, let $\rho$ be an additive Haar measure on $\iota \to \mathbb{A}_K$ and let $\mu_1$ be an additive Haar measure on $\mathbb{A}_L$ normalised so that $\mu_1(\mathrm{Box}_L) = 1$, where $\mathrm{Box}_F$ denotes the adelic box of a number field $F$: those adeles whose infinite component lies in the preimage, under the identification of $\mathbb{A}_{F,\infty}$ with the mixed space of $F$, of the fundamental domain of the $\mathbb{Z}$-lattice basis coming from the Minkowski embedding, and whose finite component is integral at every finite place. Then the box $B = \{a : \iota \to \mathbb{A}_K \mid a_i \in \mathrm{Box}_K \text{ for all } i\}$ satisfies $\rho(B) \neq 0$ and $\rho(B) \neq \infty$, and the pushforward of $\rho$ along the map $$a \longmapsto \Bigl(\sum_i (b_i \otimes a_i)\Bigr)\cdot v \in \mathbb{A}_L^2$$ equals $\rho(B) \cdot (\mu_1 \otimes \mu_1)$, the product measure on $\mathrm{Fin}\,2 \to \mathbb{A}_L$ scaled by $\rho(B)$. Here the matrix $\sum_i (b_i \otimes a_i) \in M_2(L \otimes_K \mathbb{A}_K)$, formed by applying $l \mapsto l \otimes a_i$ entrywise to $b_i$, is transported entrywise to $M_2(\mathbb{A}_L)$ by the commutativity isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L$ followed by the ring isomorphism [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57) $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ (obtained by splitting off the infinite and finite parts and base-changing each), and $v$ is mapped into $\mathbb{A}_L^2$ by the structure map $L \to \mathbb{A}_L$.
--
--   This is the measure-theoretic invariance statement underlying covolume computations on adelic vector spaces: the base change to $\mathbb{A}_K$ of a $K$-linear isomorphism $K^{\iota} \cong L^2$ is an isomorphism of locally compact groups, so it carries a Haar measure to a Haar measure, and the comparison constant is pinned down by the normalisation $\mu_1(\mathrm{Box}_L) = 1$. It is used in the computation of the integral of a Schwartz function against the pair Haar measure, where the resulting factor $\rho(\mathrm{Box}_K^{\iota})$ appears together with the Gram determinant and the discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.map_mulVec_sum_map_tmul_eq_measure_pi_adelicBox_smul_pi_of_linearIndependent_of_span_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (v : Fin 2 → L)
    (hli : LinearIndependent K fun i => (b i).mulVec v)
    (hsp : Submodule.span K (Set.range fun i => (b i).mulVec v) = ⊤)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (ρ : Measure (ι → AdeleRing (𝓞 K) K)) [ρ.IsAddHaarMeasure]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] (hμ₁ : μ₁ (adelicBox L) = 1) :
    ρ {a | ∀ i, a i ∈ adelicBox K} ≠ 0 ∧ ρ {a | ∀ i, a i ∈ adelicBox K} ≠ ⊤ ∧
    Measure.map (fun a : ι → AdeleRing (𝓞 K) K =>
        ((∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i).map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)).mulVec
          fun j => algebraMap L (AdeleRing (𝓞 L) L) (v j)) ρ =
      ρ {a | ∀ i, a i ∈ adelicBox K} • Measure.pi fun _ : Fin 2 => μ₁ := by sorry
