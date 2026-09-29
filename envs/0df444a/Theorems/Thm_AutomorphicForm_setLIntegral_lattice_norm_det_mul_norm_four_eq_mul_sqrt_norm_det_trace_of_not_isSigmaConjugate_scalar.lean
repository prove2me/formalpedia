-- Prove2me | Theorems.Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
-- name    : AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/b1def677-d4c1-5188-a967-4f8c83259ac5
-- title:
--   Local lattice covolume at a non-split place
-- statement:
--   Let $K \subset L$ be number fields with $[L:K]=2$, let $\sigma$ be a $K$-automorphism of $L$ generating the full automorphism group (every $\tau$ lies in the subgroup of integer powers of $\sigma$), let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbf{A}_K$ and $u$ a unit of $\mathbf{A}_K$, and put $\delta := \delta_0 \cdot c\,I$ in $\mathrm{GL}_2(L \otimes_K \mathbf{A}_K)$, the image of $\delta_0$ being taken along $l \mapsto l \otimes 1$. Assume the norm string of $\delta$, i.e. the product of $(\mathrm{id} \otimes \sigma)$-iterates $\delta \cdot \sigma(\delta)$ (a product of $[L:K]$ factors), equals the image of the central scalar $u\,I$ of $\mathrm{GL}_2(\mathbf{A}_K)$ under $a \mapsto 1 \otimes a$, and that $\delta_0$ is $\sigma$-conjugate to no scalar over $L$: $x^{-1}\delta_0\,\sigma(x) \neq z\,I$ for all $x \in \mathrm{GL}_2(L)$, $z \in L^\times$. Fix a height-one prime $v$ of $\mathcal{O}_K$ and let $\delta_v \in \mathrm{GL}_2(L \otimes_K K_v)$ be the image of $\delta$. Let $T'_v := \{t : t\,\delta_v\,\sigma(t)^{-1} = \delta_v\}$ be the $\sigma$-twisted centralizer, carrying its Borel structure, let $\tau$ be a Haar measure on $T'_v$ and $t_v \in [0,\infty]$. Assume $\delta_v$ is $\sigma$-conjugate to no scalar $z\,I$, $z \in (L \otimes_K K_v)^\times$, and the normalisation $\tau(S)\cdot N(v) = t_v + \tau(S)$, where $S \subset T'_v$ is the set of $t$ whose determinant is $1 \otimes s$ for some $s \in K_v^\times$ with $|s|_v = 1$ and $N(v)$ is the absolute norm of $v$. Finally let $b : \iota \to M_2(L)$, $\iota$ a finite type with decidable equality, be $K$-linearly independent with $K$-span exactly the twisted commutant $\{X : X\delta_0 = \delta_0\,\sigma(X)\}$. Then $$\Bigl(\int^-_{\Lambda} \bigl\lVert N_{(L\otimes_K K_v)/K_v}(\det t)\bigr\rVert \, d\tau\Bigr)\cdot \lVert 4 \rVert = t_v \cdot \sqrt{\bigl\lVert \det\bigl(\mathrm{Tr}_{L/K}\,\mathrm{tr}(b_i b_j)\bigr)_{i,j}\bigr\rVert} \cdot \bigl(1 - N(v)^{-2}\bigr)^{-1}\bigl(1 - N(v)^{1-2}\bigr)^{-1},$$ where $\Lambda$ is the set of $t \in T'_v$ whose matrix is $\sum_k (b_k \text{ entrywise } \otimes a_k)$ for some $a : \iota \to K_v$ with all $a_k$ in the valuation ring of $K_v$, the norms are the $v$-adic absolute values (the Gram determinant being formed in $K$ and then mapped to $K_v$), and all quantities are extended non-negative reals.
--
--   This is the local covolume computation at a finite place of the second kind, where the local twisted centralizer is the unit group of a division quaternion algebra over $K_v$: the $\tau$-mass, weighted by the modulus of the reduced norm, of the reference lattice spanned over $\mathcal{O}_v$ by a $K$-basis of the twisted commutant is expressed through the discriminant of the trace form and the local Euler factors. It feeds the global covolume identity used in comparing adelic box measures with the twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar.lean

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox
  NumberField.TateGlobal IsDedekindDomain AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

theorem AutomorphicForm.setLIntegral_lattice_norm_det_mul_norm_four_eq_mul_sqrt_norm_det_trace_of_not_isSigmaConjugate_scalar
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : HeightOneSpectrum (𝓞 K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτ : τ.IsHaarMeasure) (tv : ℝ≥0∞)
    (hnsc : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (hshell : τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        tv +
          τ {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b)) :
    (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          ∃ a : ι → v.adicCompletion K, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) *
        ENNReal.ofReal ‖(4 : v.adicCompletion K)‖ =
      tv * ENNReal.ofReal (Real.sqrt ‖algebraMap K (v.adicCompletion K) (Matrix.of fun i j : ι => Algebra.trace K L (Matrix.trace (b i * b j))).det‖) *
        ((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (-(2 : ℝ)))⁻¹ * (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0∞) ^ (1 - (2 : ℝ)))⁻¹) := by sorry
