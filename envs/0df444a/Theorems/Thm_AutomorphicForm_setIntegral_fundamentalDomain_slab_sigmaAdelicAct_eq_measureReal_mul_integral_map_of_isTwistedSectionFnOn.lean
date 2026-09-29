-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
-- name    : AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fcaa3b3c-2aa7-507d-a056-bdafa010a06d
-- title:
--   Twisted slab identity: covolume times twisted orbital integral
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, extending the action on $L$ and continuous), and let $\sigma \in \mathrm{Gal}(L/K)$. Write $E$ for the entrywise map on $\mathrm{GL}_2$ induced by the ring isomorphism $L\otimes_K\mathbb A_K \cong \mathbb A_K\otimes_K L \cong \mathbb A_L$ obtained from [`M4aHerbrand.Bridge.genuineRingEquiv`](def/M4aHerbrand_GenuineTensorEquiv.html#L57) after interchanging the factors, and $\sigma_{\mathrm{GL}}$ for the entrywise map induced by $\sigma\otimes\mathrm{id}$ on $L\otimes_K\mathbb A_K$. Fix $\delta_0\in\mathrm{GL}_2(L)$ and a unit $c$ of $L\otimes_K\mathbb A_K$, and put $\delta=(\delta_0\otimes 1)\cdot c\,I$. Let $T'=\{t : t\delta\,\sigma_{\mathrm{GL}}(t)^{-1}=\delta\}\subseteq \mathrm{GL}_2(L\otimes_K\mathbb A_K)$, taken with its Borel structure, and let $\tau'$ be a Haar measure on $T'$ that is also right invariant. Let $\Gamma'=\{t\in\mathrm{GL}_2(L): t\delta_0\,\sigma(t)^{-1}=\delta_0\}$, let $D'\subseteq T'$ be a fundamental domain for the right multiplication action on $T'$ of the image of $\Gamma'$ under $l\mapsto l\otimes 1$ (as a subgroup of $T'$), with respect to $\tau'$. Let $\alpha,\beta\in\mathbb R$ with $0<\alpha$, let $\mu$ be the Haar measure of $\mathrm{GL}_2(\mathbb A_L)$ restricted to the slab $\{g:\|\det g\|_L\in[\alpha,\beta]\}$, where $\|\cdot\|_L$ is the module of an idele for the distributive Haar character, and let $\Psi$ be a fundamental domain for the left multiplication action of $\Gamma'$, embedded in $\mathrm{GL}_2(\mathbb A_L)$ through $L\to\mathbb A_L$, with respect to $\mu$. Let $\varphi:\mathrm{GL}_2(\mathbb A_L)\to\mathbb C$ be measurable and $w:\mathrm{GL}_2(L\otimes_K\mathbb A_K)\to\mathbb R$ satisfy `IsTwistedSectionFnOn` for $\delta$, $\tau'$ and $\varphi\circ E$: $w\ge 0$, $w$ measurable with compact support, and $\int_{T'}w(tx)\,d\tau'=1$ for every $x$ with $(\varphi\circ E)(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x))\neq 0$. Then $$\int_{\Psi}\varphi\bigl(x^{-1}\,\delta_0\,\sigma_D(x)\,E(c\,I)\bigr)\,d\mu = \tau'\bigl(D'\cap\{t:\|\det E(t)\|_L\in[\alpha,\beta]\}\bigr)\cdot\int (\varphi\circ E)\bigl(y^{-1}\delta\,\sigma_{\mathrm{GL}}(y)\bigr)\,w(y)\,d\nu,$$ where $\delta_0$ is viewed in $\mathrm{GL}_2(\mathbb A_L)$ through $L\to\mathbb A_L$, $\sigma_D$ is the entrywise action of $D(\sigma)$ on $\mathrm{GL}_2(\mathbb A_L)$, the covolume is taken as a real number and coerced to $\mathbb C$, and $\nu$ is the pushforward of the Haar measure of $\mathrm{GL}_2(\mathbb A_L)$ along $E^{-1}$, the target carrying the Borel structure [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57).
--
--   This is the twisted analogue, for a single $\sigma$-twisted class, of the computation of the contribution of a conjugacy class to an integral over a slab $\alpha\le\|\det\|_L\le\beta$: the contribution factors as the slab covolume of a fundamental domain for the rational twisted centralizer inside the adelic twisted centralizer, times the twisted orbital integral of $\varphi$ at $\delta$ expressed through the section function $w$. It is the form in which twisted orbital integrals enter the comparison with orbital integrals over $K$ in cyclic base change for $\mathrm{GL}(2)$, and it is used by the two results evaluating integrals over $\sigma$-centralizer domains in terms of values at central scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.twistedCentralizerBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_sigmaAdelicAct_eq_measureReal_mul_integral_map_of_isTwistedSectionFnOn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    [τ'.IsHaarMeasure] [τ'.IsMulRightInvariant]
    (D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hD' : IsFundamentalDomain
      (((AutomorphicForm.sigmaCentralizer
          (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom :
              L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
        (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ
          (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom :
                L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
            Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ')
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L))
    (hΨ : IsFundamentalDomain
      ((AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
        (AutomorphicForm.globalPoints (𝓞 L) L)) Ψ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφm : Measurable φ)
    (w : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ)
    (hw : AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ'
      (φ ∘ Matrix.GeneralLinearGroup.map
        (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
          (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)) w) :
    ∫ x in Ψ, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
          AutomorphicForm.sigmaAdelicAct K L D σ x *
        Matrix.GeneralLinearGroup.map
          (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
            (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) c))
        ∂((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
          {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) =
      (τ'.real (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc α β}) : ℂ) *
        ∫ y, (φ ∘ Matrix.GeneralLinearGroup.map
            (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
              (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom))
              (y⁻¹ *
                (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
                  Matrix.GeneralLinearGroup.scalar (Fin 2) c) *
                AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ y) * (w y : ℂ)
          ∂(@Measure.map (AutomorphicForm.AdelicGL2 (𝓞 L) L) (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _
            (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K))
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).symm.toRingHom))
            (adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
