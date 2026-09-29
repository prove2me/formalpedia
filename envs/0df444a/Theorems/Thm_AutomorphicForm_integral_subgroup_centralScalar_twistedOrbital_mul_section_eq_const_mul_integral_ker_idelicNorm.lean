-- Prove2me | Theorems.Thm_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
-- name    : AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/57ca693c-9676-52d4-a457-26a7b5b958f3
-- title:
--   Unfolding the H-fibre of a twisted orbital integral
-- statement:
--   Let $L/K$ be a Galois extension of number fields with $\sigma \in \mathrm{Gal}(L/K)$ such that every element of the group lies in $\langle\sigma\rangle$, and let $D$ supply a Galois action on the adeles of $L$ (a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}(\mathbb{A}_L)$, continuous and compatible with $L\hookrightarrow\mathbb{A}_L$). Fix Haar measures $\nu_{Z_L}$ on $\mathbb{A}_L^\times$ and $\nu_K$ on $\mathbb{A}_K^\times$. Let $H\le \mathrm{GL}_2(\mathbb{A}_L)$ be closed and consist exactly of those $h$ whose $(1,0)$ and $(0,1)$ entries vanish and for which $(\sigma\cdot h)h^{-1}$ is central, carry a right-invariant Haar measure $\mu_H$, and admit a chart with constant $c_H>0$: integrating any $g$ over $H$ gives $c_H$ times the integral of $g\bigl(\mathrm{centralScalar}(z)\cdot \mathrm{baseChangeGL}(\mathrm{toTensorGL}(\mathrm{diag}(a,1)))\bigr)$ over $(z,a)$ for $\nu_{Z_L}\otimes\nu_K$. Let $A_K\le\mathbb{A}_L^\times$ be the closed image of $\mathbb{A}_K^\times$ under the unit map of the base-change homomorphism $\beta$, with Haar measure $\mu_{A_K}$ pushed forward from $\nu_K$; let $N^1$ be the closed kernel of the idelic norm, with Haar $\mu_N$ satisfying, for a constant $c_N>0$, that integration over $N^1$ equals $c_N$ times the integral of $g\bigl((\sigma\cdot u)u^{-1}\bigr)$ over representatives $u$ of the $A_K$-orbit quotient for the Haar quotient measure built from $\nu_{Z_L},\mu_{A_K}$. Let $t\in\mathrm{GL}_2(L)$ be diagonal with $N_{L/K}(t_{00}/t_{11})\ne 1$, and $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ with $\mathrm{baseChangeGL}(\delta)$ the adelic image of $t$. Let $\tau$ be a Haar measure on the $\sigma$-twisted centraliser $\{x : x\,\delta\,(\sigma x)^{-1}=\delta\}$ (with its Borel structure) satisfying, for a constant $c_\tau>0$, that integration over it equals $c_\tau$ times the integral of $g(\mathrm{toTensorGL}(\mathrm{diag}(a_1,a_2)))$ over $\nu_K\otimes\nu_K$. Let $\varphi$ be continuous with compact support on $\mathrm{GL}_2(\mathbb{A}_L)$, let $w\in\mathbb{A}_L^\times$, and let $s\ge 0$ be continuous with compact support on $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ and such that $\int s(rx)\,d\tau(r)=1$ whenever $\varphi\bigl(\mathrm{centralScalar}(w)\cdot\mathrm{baseChangeGL}(x^{-1}\delta\,\sigma x)\bigr)\ne 0$. Then for every $q\in \mathrm{GL}_2(\mathbb{A}_L)$, $$\int_H \varphi\bigl(\mathrm{centralScalar}(w)\,(hq)^{-1}\,t\,(\sigma\cdot(hq))\bigr)\,s\bigl(\mathrm{baseChangeGLEquiv}^{-1}(hq)\bigr)\,d\mu_H = \frac{c_H}{c_\tau c_N}\int_{N^1}\varphi\bigl(q^{-1}\,t\,\mathrm{centralScalar}(nw)\,(\sigma\cdot q)\bigr)\,d\mu_N,$$ where $t$ denotes its adelic image and $\sigma\cdot$ the action induced by $D$.
--
--   This is the torus step in the unfolding of a twisted orbital integral for $\mathrm{GL}(2)$ over a cyclic extension: the integral over the diagonal-modulo-centre subgroup $H$ collapses, by way of the $A_K$-quotient and the section property of $s$, to an integral over the norm-one ideles. It is used in the identification of twisted orbital integrals of functions pulled back along base change with the corresponding orbital integrals on the norm-one group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm.lean

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
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_subgroup_centralScalar_twistedOrbital_mul_section_eq_const_mul_integral_ker_idelicNorm

    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure]
    (cH : ℝ) (hcH : 0 < cH)
    (hHc : ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
      ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
        cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
            AutomorphicForm.baseChangeGL K L
              (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK))
    (cτ : ℝ) (hcτ : 0 < cτ)
    (AK : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hAKc : IsClosed (AK : Set (AdeleRing (𝓞 L) L)ˣ))
    (hAK : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ AK ↔ ∃ a : (AdeleRing (𝓞 K) K)ˣ,
      z = Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a)
    (μAK : Measure AK) [μAK.IsHaarMeasure]
    (hμAK : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ a : AK, g (a : (AdeleRing (𝓞 L) L)ˣ) ∂μAK =
        ∫ a, g (Units.map (M4aHerbrand.GenuineDescent.genuineBaseChange K L).β.toMonoidHom a) ∂νK)
    (N1 : Subgroup (AdeleRing (𝓞 L) L)ˣ) (hN1c : IsClosed (N1 : Set (AdeleRing (𝓞 L) L)ˣ))
    (hN1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, z ∈ N1 ↔
      (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z = 1)
    (μN : Measure N1) [μN.IsHaarMeasure]
    (cN : ℝ) (hcN : 0 < cN)
    (hNc : ∀ g : (AdeleRing (𝓞 L) L)ˣ → ℂ,
      ∫ n : N1, g (n : (AdeleRing (𝓞 L) L)ˣ) ∂μN =
        cN * ∫ q : MulAction.orbitRel.Quotient AK (AdeleRing (𝓞 L) L)ˣ,
          g (D.unitsAct σ q.out * (q.out)⁻¹) ∂(HaarQuotient.measure νZL AK μAK))
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t)
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (hτc : ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
        cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
          g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (w : (AdeleRing (𝓞 L) L)ˣ)

    (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℝ) (hsc : Continuous s) (hs0 : ∀ x, 0 ≤ s x)
    (hss : HasCompactSupport s)
    (hsec : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φ (AutomorphicForm.centralScalar (𝓞 L) L w *
          AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x)) ≠ 0 →
        ∫ r : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          s ((r : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) * x) ∂τ = 1)
    (q : AdelicGL2 (𝓞 L) L) :
    ∫ h : H, φ (AutomorphicForm.centralScalar (𝓞 L) L w *
          (((h : AdelicGL2 (𝓞 L) L) * q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ ((h : AdelicGL2 (𝓞 L) L) * q))) *
        (s ((AutomorphicForm.baseChangeGLEquiv K L).symm ((h : AdelicGL2 (𝓞 L) L) * q)) : ℂ) ∂μH =
      ((cH / (cτ * cN) : ℝ) : ℂ) *
        ∫ n : N1, φ ((q)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
          (AutomorphicForm.centralScalar (𝓞 L) L ((n : (AdeleRing (𝓞 L) L)ˣ) * w) *
            AutomorphicForm.sigmaAdelicAct K L D σ q)) ∂μN := by sorry
