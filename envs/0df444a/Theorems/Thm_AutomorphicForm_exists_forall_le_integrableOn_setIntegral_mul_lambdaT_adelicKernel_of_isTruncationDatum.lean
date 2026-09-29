-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum
-- name    : AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/3c96ecc9-3b68-5e8c-a940-74e76f6ef891
-- title:
--   Integrability of the centre-folded truncated GL₂ adelic kernel
-- statement:
--   Let $K$ be a number field with adele ring $\mathbb A_K$, and let $0<\alpha<\beta$ be reals. Let $d=((c,u,d_1,d_2),T_c,\Phi_0)$ satisfy `IsTruncationDatum K α β d`, i.e. $c>0$, $T_c\subseteq\mathrm{GL}_2(\mathbb A_K)$ is compact, $\Phi_0$ is contained in the union over $y\in T_c$ of the right translates by $y$ of the centre-cut Siegel set of $K$ with parameters $(c,u,d_1,d_2)$ (finite component in the integral part, all local heights $\ge c$, all window quantities $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$), $\Phi_0$ is contained in the determinant slab $\{g:\|\det g\|\in[\alpha,\beta]\}$, and $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb A_K)$ with respect to the Haar measure `adelicGLHaar` restricted to that slab. Let $\nu_Z$ be a Haar measure on $\mathbb A_K^\times$ (with its Borel structure) and $\Omega_K$ a fundamental domain for the image of $K^\times$ in $\mathbb A_K^\times$ with respect to $\nu_Z$; let $\xi$ be a homomorphism from $\mathbb A_K^\times$ (as the top subgroup) to $\mathbb C^\times$ which is continuous as a $\mathbb C$-valued function and trivial on the image of $K^\times$. Let $f:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be factorizable, i.e. $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean and $f_{\mathrm{fin}}$ a finite test factor. Then there is $R_0\in\mathbb R$ such that for every $R\ge R_0$ the function $$x\mapsto\int_{\Omega_K}\xi(z)\,\bigl(\Lambda^{e^R}\,y\mapsto\textstyle\sum_{\gamma\in\mathrm{GL}_2(K)}f(x^{-1}\gamma y)\bigr)(z\cdot x)\,d\nu_Z(z)$$ is integrable on $\Phi_0$ with respect to `adelicGLHaar`; here $z\cdot x$ means the central scalar matrix of $z$ times $x$, and $\Lambda^{T}\varphi=\varphi-\mathbf 1_{\{H>T\}}\cdot(\text{constant term of }\varphi\text{ along }t\mapsto\binom{1\ t}{0\ 1})$, the constant term taken against the adelic additive Haar measure conditioned on the adelic box and $H$ the adelic height.
--
--   This is the convergence statement underlying the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field, in the form with a central character (the kernel folded over the centre against $\xi$) and with the naive one-cusp truncation at cutoff $e^R$, on a truncation domain of a determinant slab covered by compact translates of a Siegel set of positive height floor. It is used by the subsequent decomposition of the truncated integral into its central-elliptic and parabolic contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_le_integrableOn_setIntegral_mul_lambdaT_adelicKernel_of_isTruncationDatum
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (d : (ℝ × ℝ × ℝ × ℝ) × Set (AdelicGL2 (𝓞 K) K) × Set (AdelicGL2 (𝓞 K) K))
    (hd : AutomorphicForm.IsTruncationDatum K α β d)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K =>
          ∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            @AutomorphicForm.lambdaT _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K) _ _
              (@ProbabilityTheory.cond _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
                (NumberField.AdelicHaar.adelicAddHaar (𝓞 K) K) (NumberField.AdelicBox.adelicBox K))
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
              (fun y => AutomorphicForm.adelicKernel K f x y)
              (AutomorphicForm.centralScalar (𝓞 K) K z * x) ∂νZK)
        d.2.2 (adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
