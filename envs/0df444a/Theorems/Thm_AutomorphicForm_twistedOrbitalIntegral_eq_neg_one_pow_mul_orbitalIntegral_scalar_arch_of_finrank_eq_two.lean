-- Prove2me | Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
-- name    : AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/68b4ca30-32e4-5e3c-bb54-25c2a5cbe935
-- title:
--   Archimedean twisted orbital integral at a central norm class
-- statement:
--   Let $K \subset L$ be number fields with $[L:K]=2$ and let $\sigma$ be a $K$-automorphism of $L$ generating the whole automorphism group (every $\tau$ lies in the subgroup of integer powers of $\sigma$). Let $\gamma \in GL_2(K_\infty)$, where $K_\infty$ is the infinite adele ring of $K$, be a scalar matrix $c\cdot 1$ for some unit $c$, and let $\delta, y \in GL_2(L\otimes_K K_\infty)$ satisfy `IsNormConjugator`, i.e. the image of $\gamma$ in $GL_2(L\otimes_K K_\infty)$ equals $y^{-1}\,(\text{norm string of }\delta\text{ for }\sigma)\,y$. Let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $GL_2(K_\infty)$ and $\tau'$ a Haar measure on the $\sigma$-twisted centraliser of $\delta$, both with their Borel structures. A normalisation hypothesis is assumed: with $\mathbb{R}$-algebra structures on $K_\infty$ and on $L\otimes_K K_\infty$ coming from the mixed-space description and from inclusion on the right factor, there exist $n_1,n_2$, $\mathbb{R}$-linearly independent families $e_1,e_2$ of matrices in $M_2(L\otimes_K K_\infty)$ spanning respectively the image of $M_2(K_\infty)$ and $\{X : X\delta = \delta\,\sigma(X)\}$, and one scalar $s \neq 0,\infty$ such that the pushforwards of $\tau$ and $\tau'$ into $M_2(L\otimes_K K_\infty)$ are both $s$ times the Gram-normalised Lebesgue measure on the respective span (scaled by $\sqrt{|\det(\mathrm{Tr}_{\mathbb{R}}\,\mathrm{tr}(e_i e_j))|}$), weighted by $|N_{\mathbb{R}}(\det X)|^{-1}$. Then for every $\varphi_a$ on $GL_2(L_\infty)$ and $f_a$ on $GL_2(K_\infty)$ which are archimedean test factors (each given by a smooth function of the matrix entries in the mixed space, with compact support) and which match in the sense of `AreMatchingArch`, and for all complex numbers $I, I'$ such that $I'$ is a twisted orbital integral of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta$ against $\tau'$ and the archimedean Haar measure on $GL_2(L\otimes_K K_\infty)$, and $I$ is an orbital integral of $f_a$ at $\gamma$ against $\tau$ and the archimedean Haar measure on $GL_2(K_\infty)$, one has $I' = (-1)^r I$, where $r$ is the number of infinite places $w$ of $K$ at which the $w$-component of $\delta$ is not $\sigma$-conjugate to any scalar in $GL_2(L\otimes_K K_w)$.
--
--   This is the archimedean block of the comparison of twisted and ordinary orbital integrals in quadratic base change for $GL(2)$ at a central norm class: the sign $(-1)^r$ records the places where the local class is of quaternionic type. It feeds the global matching statement [`AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ')
    (hnorm :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
      ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
        AutomorphicForm.AreMatchingArch K L σ φa fa →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = (-1 : ℂ) ^ (Nat.card {w : NumberField.InfinitePlace K //
            ∀ z : (L ⊗[K] w.Completion)ˣ,
              ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
                  (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.map (AlgHom.id K L)
                      (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom δ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}) * I := by sorry
