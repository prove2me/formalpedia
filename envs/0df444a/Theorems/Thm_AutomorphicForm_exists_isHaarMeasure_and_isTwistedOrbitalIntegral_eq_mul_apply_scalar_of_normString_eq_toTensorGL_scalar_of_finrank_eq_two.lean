-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d1021de4-8b33-54c6-8a66-8abbe2034eda
-- title:
--   Local twisted orbital integral at a central norm, degree two
-- statement:
--   Let $K \subseteq L$ be number fields with $\operatorname{finrank}_K L = 2$, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the completion and $E = L \otimes_K K_v$, let $c \in K_v^{\times}$, and let $\delta \in \mathrm{GL}_2(E)$ satisfy that its norm string $\prod_{i<2} (\mathrm{sigmaGL}\,\sigma)^{i}(\delta)$ equals the image of the scalar matrix $\mathrm{scalar}(c)$ under [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71), the map on $\mathrm{GL}_2$ induced by $K_v \to E$, $x \mapsto 1 \otimes x$. Let $\tau'$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser of $\delta$, let $\varphi_v$ on $\mathrm{GL}_2(E)$ and $f_v$ on $\mathrm{GL}_2(K_v)$ be complex-valued, locally constant and compactly supported, and assume the pair $(\varphi_v, f_v)$ satisfies [`AutomorphicForm.AreMatchingLocal`](def/AutomorphicForm_TwistedOrbital.html#L386), that is `AreMatchingOn` for $\sigma$ with the measures `semiLocalHaar K L v` and `localHaar K v`. Then, for the Borel structures on $\mathrm{GL}_2(K_v)$, on $\mathrm{GL}_2(E)$ and on the twisted centraliser, there exist Haar measures $\tau_v$ on $\mathrm{GL}_2(K_v)$ and $\tau_v'$ on the twisted centraliser and nonzero $\alpha, \beta \in \mathbb{R}_{\geq 0}$ with $\mathrm{localHaar}\,K\,v = \alpha \cdot \tau_v$ and $\tau' = \beta \cdot \tau_v'$, such that three further assertions hold. First, a dichotomy: either there is $y \in \mathrm{GL}_2(E)$ with $\mathrm{toTensorGL}(\mathrm{scalar}(c)) = y^{-1} \cdot (\text{norm string of } \delta) \cdot y$ for which the pushforward of $\tau_v'$ along $t \mapsto y^{-1} t y$ equals the pushforward of $\tau_v$ along `toTensorGL`; or no scalar matrix $\mathrm{scalar}(z)$, $z \in E^{\times}$, is of the form $x^{-1}\delta\,\sigma(x)$, and, writing $S$ for the set of $t$ in the twisted centraliser whose determinant is the image of some $s \in K_v^{\times}$ of valuation $1$, one has $\tau_v'(S) \cdot \lvert \mathcal{O}_K/v \rvert = \tau_v(\mathrm{localIntegralSet}\,K\,v) + \tau_v'(S)$, the product and sum taken in $\overline{\mathbb{R}}_{\geq 0}$. Second, if $\delta$ is $\sigma$-conjugate to some scalar matrix then $\beta = 1$. Third, for every $J \in \mathbb{C}$ that is a twisted orbital integral of $\varphi_v$ at $\delta$ for $\tau'$ (in the sense of `IsTwistedOrbitalIntegral`, taken with `semiLocalHaar K L v`): if $\delta$ is $\sigma$-conjugate to no scalar matrix then $J = -f_v(\mathrm{scalar}(c))\,\alpha\,\beta^{-1}$, and if $\delta$ is $\sigma$-conjugate to a scalar matrix then $J = f_v(\mathrm{scalar}(c))\,\alpha\,\beta^{-1}$.
--
--   This is the local comparison of twisted and ordinary orbital integrals at a class whose norm is central, at a finite place of $K$ in a quadratic extension, treating both kinds of class at once and producing from an arbitrary Haar measure on the twisted centraliser a compatibly normalised pair of local measures together with the resulting value of the twisted orbital integral. It is used in the global comparison of twisted and untwisted trace-formula contributions from central classes, namely by [`AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.mul_eq_mul_of_isTwistedOrbitalIntegralOn_of_isOrbitalIntegralOn_centralScalar_of_forall_ne_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.exists_isHaarMeasure_and_isTwistedOrbitalIntegral_eq_mul_apply_scalar_of_normString_eq_toTensorGL_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ')
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (hm : AutomorphicForm.AreMatchingLocal K L v σ φv fv) :
    letI := AutomorphicForm.localGLBorel K v
    letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ
    ∃ (τv : Measure (GL (Fin 2) (v.adicCompletion K)))
      (τv' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (α β : ℝ≥0),
      τv.IsHaarMeasure ∧ τv'.IsHaarMeasure ∧ α ≠ 0 ∧ β ≠ 0 ∧
      AutomorphicForm.localHaar K v = α • τv ∧ τ' = β • τv' ∧
      ((∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y ∧
          Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ) =>
              y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) τv' =
            Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) τv) ∨
        ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
            ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
          τv' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
              Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
                Units.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
            (Ideal.absNorm v.asIdeal : ENNReal) =
          τv (AutomorphicForm.localIntegralSet K v) +
            τv' {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
              Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
                Units.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s})) ∧
      ((∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
          AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) →
        β = 1) ∧
      ∀ J : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ' φv J →
        ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
            ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) →
          J = -(fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (α : ℂ) * ((β⁻¹ : ℝ≥0) : ℂ))) ∧
        ((∃ z : (L ⊗[K] v.adicCompletion K)ˣ,
            AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) →
          J = fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) * (α : ℂ) * ((β⁻¹ : ℝ≥0) : ℂ)) := by sorry
