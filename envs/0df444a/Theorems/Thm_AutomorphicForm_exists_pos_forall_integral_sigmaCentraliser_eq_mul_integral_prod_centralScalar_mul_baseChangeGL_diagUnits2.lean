-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2
-- name    : AutomorphicForm.exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/c590e30f-6ead-5434-93c2-c92deb89e284
-- title:
--   Haar integration on the σ-twisted diagonal centraliser of GL₂(A_L)
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let the unit group $(\mathbb{A}_L)^\times$ of the adele ring of $L$ carry a measurable structure that is the Borel structure of its topology together with a Haar measure $\nu_{Z_L}$, and likewise let $(\mathbb{A}_K)^\times$ carry its Borel structure and a Haar measure $\nu_K$; the group $\mathrm{GL}_2(\mathbb{A}_L)$ is measured with its Borel structure. Let $D$ be an idelic Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each $\tau$ and extends the action on $L$ through the structure map, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $H \le \mathrm{GL}_2(\mathbb{A}_L)$ be a closed subgroup whose members are exactly those $h$ whose off-diagonal entries $h_{10}$ and $h_{01}$ vanish and for which $\sigma_D(h)h^{-1}$ is central, where $\sigma_D$ denotes the entrywise action of the ring automorphism $D.\mathrm{act}\,\sigma$ on $\mathrm{GL}_2(\mathbb{A}_L)$, and let $\mu_H$ be a Haar measure on $H$ that is in addition right invariant. The assertion is the existence of a real constant $c_H > 0$ such that for every function $g : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ whatsoever, with no measurability or integrability hypothesis, $$\int_H g(h)\,d\mu_H(h) \;=\; c_H \int_{(\mathbb{A}_L)^\times \times (\mathbb{A}_K)^\times} g\bigl(z \cdot I_2 \cdot \mathrm{bc}(\mathrm{diag}(a,1))\bigr)\, d(\nu_{Z_L} \otimes \nu_K)(z,a),$$ both sides being Bochner integrals; here $z \cdot I_2$ is the central scalar matrix attached to the idele $z$, $\mathrm{diag}(a,1) \in \mathrm{GL}_2(\mathbb{A}_K)$ is the diagonal matrix with entries $a$ and $1$, and $\mathrm{bc}$ is the composite of the inclusion $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ induced by the right factor embedding with the isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$.
--
--   This identifies, up to a positive constant, Haar measure on the $\sigma$-twisted centraliser of the diagonal torus in $\mathrm{GL}_2(\mathbb{A}_L)$ with the push-forward of the product of idelic Haar measures on $(\mathbb{A}_L)^\times \times (\mathbb{A}_K)^\times$ along $(z,a) \mapsto z I_2 \cdot \mathrm{bc}(\mathrm{diag}(a,1))$, the normalisation needed for the hyperbolic (twisted orbital) terms of the twisted trace formula for a cyclic extension $L/K$. It is stated for arbitrary complex-valued $g$, so that it can be applied as a rewriting rule, and is used in the estimation of twisted orbital integrals over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2.lean

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

theorem AutomorphicForm.exists_pos_forall_integral_sigmaCentraliser_eq_mul_integral_prod_centralScalar_mul_baseChangeGL_diagUnits2
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
    [νK.IsHaarMeasure] :
    ∃ cH : ℝ, 0 < cH ∧
      ∀ g : AdelicGL2 (𝓞 L) L → ℂ,
        ∫ h : H, g (h : AdelicGL2 (𝓞 L) L) ∂μH =
          cH * ∫ p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.centralScalar (𝓞 L) L p.1 *
              AutomorphicForm.baseChangeGL K L
                (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.2 1))) ∂(νZL.prod νK) := by sorry
