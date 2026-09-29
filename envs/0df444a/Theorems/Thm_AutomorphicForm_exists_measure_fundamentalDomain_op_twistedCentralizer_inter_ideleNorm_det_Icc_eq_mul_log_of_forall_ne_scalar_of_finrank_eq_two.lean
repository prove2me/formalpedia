-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
-- name    : AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/3b358418-aa1c-5b8c-a5cf-a46727600cd0
-- title:
--   Log-linear band covolume for twisted centralizers in degree two
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois of degree $2$ (the hypothesis $\operatorname{finrank}_K L = 2$), let $\sigma$ be a $K$-automorphism of $L$ such that every $\tau \in \operatorname{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, let $\delta_0 \in \mathrm{GL}_2(L)$, let $c$ be a unit of $L \otimes_K \mathbb{A}_K$ and $u$ a unit of $\mathbb{A}_K$, and put $\delta = (\delta_0 \otimes 1)\cdot c\cdot I$, the product of the image of $\delta_0$ under $l \mapsto l \otimes 1$ with the scalar matrix of $c$, inside $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$. Here $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ entrywise through the first tensor factor ([`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202)). Two hypotheses are imposed: the norm string $\delta \cdot \sigma(\delta)$, i.e. the product $\prod_{i<2} \sigma^i(\delta)$ of [`AutomorphicForm.normString`](def/AutomorphicForm_TwistedOrbital.html#L205), equals the image under $a \mapsto 1 \otimes a$ of the scalar matrix $\operatorname{diag}(u,u) \in \mathrm{GL}_2(\mathbb{A}_K)$; and $\delta_0$ is $\sigma$-conjugate to no scalar matrix over $L$, that is $x^{-1}\delta_0\,\sigma(x) \neq z\cdot I$ for all $x \in \mathrm{GL}_2(L)$ and $z \in L^{\times}$. Let $T' = \{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the $\sigma$-twisted centralizer of $\delta$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$, equipped with the Borel $\sigma$-algebra of its subspace topology, and let $\tau'$ be a Haar measure on $T'$. The assertion is that there is a constant $C \in [0,\infty]$ with $C \neq 0$ and $C \neq \infty$ such that for every subset $D' \subseteq T'$ which is a $\tau'$-fundamental domain for the right multiplication action (the opposite group) of the subgroup $\Gamma' = \{g \in \mathrm{GL}_2(L) : g\,\delta_0\,\sigma(g)^{-1} = \delta_0\}$, pushed into $\mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ along $l \mapsto l \otimes 1$ and regarded as a subgroup of $T'$, and for all reals $0 < a \le b$, one has $$\tau'\bigl(D' \cap \{t : \|\det t\|_L \in [a,b]\}\bigr) = C \cdot \log(b/a)$$ (as an extended non-negative real), where $\|\cdot\|_L$ is the idele norm of $L$, namely the module of the distributive Haar character of $\mathbb{A}_L$, and $\det t$ is read in $\mathrm{GL}_2(\mathbb{A}_L)$ through the identification $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$.
--
--   For a twisted conjugacy class with central norm which is of the second kind, the twisted centralizer $T'$ is the idele group of a quaternion division algebra over $K$ and $\Gamma'$ is its group of global units, so the statement is the finiteness, non-vanishing and exact $\log(b/a)$ dependence of the covolume of $\Gamma'$ in the band $a \le \|\det t\|_L \le b$, for an arbitrary Haar measure; this is the normalisation required in Langlands' comparison of twisted orbital integrals in base change for $\mathrm{GL}(2)$. It is used in the evaluation of the integral over a fundamental domain of the twisted centralizer against a central character, and in the identification of the resulting rate constant in terms of the discriminant and the residue of the Dedekind zeta function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
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
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [τ'.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
        IsFundamentalDomain
          (((AutomorphicForm.sigmaCentralizer
              (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
              (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom :
                  L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
            (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
              (Matrix.GeneralLinearGroup.map
                  (Algebra.TensorProduct.includeLeftRingHom :
                    L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
            (Matrix.GeneralLinearGroup.det
              (Matrix.GeneralLinearGroup.map
                (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                  (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
                (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by sorry
