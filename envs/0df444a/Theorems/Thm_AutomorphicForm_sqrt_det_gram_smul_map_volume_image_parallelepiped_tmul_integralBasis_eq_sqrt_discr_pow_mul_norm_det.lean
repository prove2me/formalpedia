-- Prove2me | Theorems.Thm_AutomorphicForm_sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det
-- name    : AutomorphicForm.sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/adcd0e62-6c1b-5cb1-8842-5fc6d3206d16
-- title:
--   Archimedean covolume of the twisted commutant lattice
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-algebra automorphism of $L$, $\delta_0 \in \mathrm{GL}_2(L)$, and $c$ a unit of $E := L \otimes_K \mathbb{A}_{K,\infty}$, where $\mathbb{A}_{K,\infty}$ is the infinite adele ring of $K$. Let $\kappa$ be a finite type and $x : \kappa \to M_2(L)$ a family that is linearly independent over $K$ and whose $K$-span is exactly the $\sigma$-twisted commutant $\{X \in M_2(L) : X\delta_0 = \delta_0 \, \sigma(X)\}$ (hypothesis `hspan`, an iff for every $X$). Equip $\mathbb{A}_{K,\infty}$ with the $\mathbb{R}$-algebra structure transported from the mixed space $\mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$ along `InfiniteAdeleRing.ringEquiv_mixedSpace`, equip $E$ with the induced $\mathbb{R}$-algebra structure through the right inclusion, and give $M_2(E)$ its Borel $\sigma$-algebra. The assertion is: for every $n_2$ and every $\mathbb{R}$-linearly independent family $e_2 : \mathrm{Fin}\, n_2 \to M_2(E)$ whose $\mathbb{R}$-span, as a set, is $\{X : X\delta = \delta \cdot X.\mathrm{map}(\sigma \otimes \mathrm{id})\}$, with $\delta$ the product of the image of $\delta_0$ under $l \mapsto l \otimes 1$ with the scalar matrix $c$ and $\sigma \otimes \mathrm{id}$ the ring endomorphism [`AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ`](def/AutomorphicForm_TwistedOrbital.html#L199) of $E$, the Gram-normalised measure $\sqrt{\left|\det\left(\mathrm{Tr}_{E/\mathbb{R}}\,\mathrm{tr}(e_2(i)e_2(j))\right)\right|}$ times the pushforward of Lebesgue measure on $\mathbb{R}^{n_2}$ along $a \mapsto \sum_i a_i e_2(i)$ assigns to the half-open parallelepiped $\{\sum_p t_p \, x_{p_2}.\mathrm{map}(l \mapsto l \otimes \omega_{p_1}) : t \in [0,1)\}$, indexed by pairs consisting of an index of the integral basis $\omega$ of $\mathcal{O}_K$ and an element of $\kappa$, the value $\sqrt{|d_K|^{\#\kappa} \cdot \left|N_{K/\mathbb{Q}}\det\left(\mathrm{Tr}_{L/K}\,\mathrm{tr}(x_i x_j)\right)\right|}$ in $[0,\infty]$.
--
--   This computes the archimedean covolume of the lattice spanned by $x_i \otimes \omega_a$ inside the twisted commutant of $\delta$ in $M_2(E)$, measured with respect to the trace-form Gram normalisation attached to an arbitrary real basis $e_2$ of that commutant; the point is that the answer depends only on the discriminant of $K$ and on the trace form of the family $x$, not on $e_2$. It feeds the construction of the normalised Haar measure used in the archimedean part of the twisted orbital integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det.lean

import Definitions.Def_AutomorphicForm_TwistedCommutant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.sqrt_det_gram_smul_map_volume_image_parallelepiped_tmul_integralBasis_eq_sqrt_discr_pow_mul_norm_det
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    {κ : Type} [Fintype κ] [DecidableEq κ] (x : κ → Matrix (Fin 2) (Fin 2) L) (hx : LinearIndependent K x)
    (hspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range x)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    ∀ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      LinearIndependent ℝ e₂ →
      (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
        {X | X * ((Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
              Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
          ((Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] InfiniteAdeleRing K) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
              Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
            X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} →
      ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
            Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
          Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume)
        ((fun t : Module.Free.ChooseBasisIndex ℤ (𝓞 K) × κ → ℝ =>
            ∑ p, t p • (x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (integralBasis K p.1))) ''
          Set.pi Set.univ (fun _ => Set.Ico (0 : ℝ) 1)) =
      ENNReal.ofReal (Real.sqrt (|(NumberField.discr K : ℝ)| ^ Fintype.card κ *
        |((Algebra.norm ℚ (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det : ℚ) : ℝ)|)) := by sorry
