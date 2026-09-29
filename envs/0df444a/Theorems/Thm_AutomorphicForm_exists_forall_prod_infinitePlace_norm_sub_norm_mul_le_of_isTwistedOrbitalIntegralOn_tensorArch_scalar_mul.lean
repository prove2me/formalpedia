-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
-- name    : AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/8a2b3d1b-c44b-5447-88d6-bf7218e92d45
-- title:
--   Archimedean twisted orbital bound, uniform in central translates
-- statement:
--   Let $L/K$ be an extension of number fields which is finite Galois with $\sigma \in \mathrm{Gal}(L/K)$ such that every element of the group lies in $\langle\sigma\rangle$ (so the extension is cyclic with generator $\sigma$), let $\nu_A$ be a Haar measure on $(K_\infty)^\times$ for the Borel structure, let $\nu$ be a Haar measure on $\mathrm{GL}_2(L \otimes_K K_\infty)$ for its Borel $\sigma$-algebra, and let $\Psi : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ satisfy `IsArchTestFactor`, i.e. $\Psi$ has compact support and is of the form $g \mapsto \Phi(\mathrm{archEntries}\, g)$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $L$. Then there is $C \ge 0$ with the following property. Let $t \in \mathrm{GL}_2(L)$ be diagonal (entries $(1,0)$ and $(0,1)$ vanish) with $N_{L/K}(t_{00}/t_{11}) \ne 1$; let $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ be such that its image under the isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ is the image of $t$ in $\mathrm{GL}_2(\mathbb{A}_L)$; write $\delta_\infty$ for the image of $\delta$ in $\mathrm{GL}_2(L \otimes_K K_\infty)$ under the map induced by $\mathbb{A}_K \to K_\infty$. Let $\tau_a$ be a Haar measure, for the Borel structure, on the $\sigma$-twisted centraliser of $\delta_\infty$ in $\mathrm{GL}_2(L \otimes_K K_\infty)$, and assume $\tau_a$ is pinned down by the requirement that for every $g : \mathrm{GL}_2(L \otimes_K K_\infty) \to \mathbb{C}$ the integral of $g$ over that centraliser against $\tau_a$ equals $\int g\bigl(\mathrm{diag}(p_1,p_2)\bigr)\, d(\nu_A \times \nu_A)(p)$ over $(K_\infty^\times)^2$, the diagonal matrices being pushed into $L \otimes_K K_\infty$ by $a \mapsto 1 \otimes a$. Finally let $c \in (L_\infty)^\times$ and $I \in \mathbb{C}$, and suppose $I$ is a twisted orbital integral at $\delta_\infty$, relative to $\nu$ and $\tau_a$, of the function $g \mapsto \Psi(c \cdot \mathrm{archIdentGL}(g))$ (multiplication by the scalar matrix $c$): that is, there is a real weight $w$ satisfying `IsTwistedSectionFnOn` for these data with $I = \int \varphi(x^{-1}\delta_\infty \sigma(x))\, w(x)\, d\nu(x)$. Then $$\Bigl(\prod_{v \mid \infty \text{ of } K} v\bigl(N_{L/K}t_{00} - N_{L/K}t_{11}\bigr)^{\mathrm{mult}(v)}\Bigr)\,\|I\| \le C\Bigl(\prod_{v \mid \infty} v\bigl(N_{L/K}t_{00}\cdot N_{L/K}t_{11}\bigr)^{\mathrm{mult}(v)}\Bigr)^{1/2}.$$
--
--   This is the archimedean slice estimate in the comparison of twisted orbital integrals for cyclic base change for $\mathrm{GL}(2)$: the regular diagonal discriminant weight times the archimedean twisted orbital integral is dominated by the square root of the product of the two norms, with a constant independent of the class $t$ and of the central translate $c$, the weight and the bound scaling in the same way under translation by the centre. It feeds the global estimate [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), where it is combined with the corresponding bounds at the finite places through the product formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul.lean

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

theorem AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    (Ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hΨ : AutomorphicForm.IsArchTestFactor L Ψ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∀ (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)) τa →
      (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
            g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) →
    ∀ (c : (InfiniteAdeleRing L)ˣ) (I : ℂ),
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
        (AutomorphicForm.tensorArch K L δ) τa
        ((fun g : GL (Fin 2) (InfiniteAdeleRing L) => Ψ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) ∘
          AutomorphicForm.archIdentGL K L) I →
      (∏ v : InfinitePlace K,
          v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) - Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^
            v.mult) * ‖I‖ ≤
        C * (∏ v : InfinitePlace K,
          v (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0) * Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1)) ^
            v.mult) ^ ((1 : ℝ) / 2) := by sorry
