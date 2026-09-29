-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
-- name    : AutomorphicForm.setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/28fbf9d6-82fe-5643-b0c4-8e56813f07fa
-- title:
--   Unfolding the centre-folded GL₂ kernel against a truncated test function
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and equip the idele unit group $(\mathbb{A}_K)^\times$ with a measurable structure that is the Borel structure of its topology, together with a Haar measure $\nu_{Z}$. Let $\xi$ be a monoid homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that $z\mapsto\xi(z)$ is continuous, $\xi$ takes the value $1$ on every idele in the image of $K^\times$ under the map induced by $K\to\mathbb{A}_K$, and $\lvert\xi(z)\rvert=1$ for all $z$. Let $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support, let $\Psi\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be measurable, vanishing outside some compact set and bounded in absolute value, and let $x\in \mathrm{GL}_2(\mathbb{A}_K)$. Write $\Phi_0$ for [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), the subset of $\mathrm{GL}_2(\mathbb{A}_K)$ read off from a chosen truncation datum for $\alpha,\beta$ (the empty set if none exists), $\iota$ for [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), the homomorphism $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A}_K)$ induced by $K\to\mathbb{A}_K$, and $z\mapsto zI$ for [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18), the homomorphism sending an idele unit to the corresponding scalar matrix. Then, with respect to the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ for the Borel structure `glBorel`, $$\int_{\Phi_0}\Bigl(\textstyle\sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}\int \xi(z)\, f\bigl(x^{-1}\,\iota(q.\mathrm{out})\,(zI\cdot y)\bigr)\,d\nu_Z(z)\Bigr)\,\Psi(y)\,dy \;=\; \bigl(\mathrm{convOp}\,f\,\theta\bigr)(x),$$ where the sums are finitely supported sums over the quotient of $\mathrm{GL}_2(K)$ by its centre with $q.\mathrm{out}$ a chosen representative, $$\theta(g)=\textstyle\sum^{\mathrm{f}}_{q}\int \xi(w)^{-1}\,\bigl(\mathbf 1_{\Phi_0}\Psi\bigr)\bigl(wI\cdot(\iota(q.\mathrm{out})\,g)\bigr)\,d\nu_Z(w),$$ and `convOp K f` sends $u$ to $g\mapsto\int u(g\,h)\,f(h)\,dh$, so that the right-hand side is $\int \theta(x h)\,f(h)\,dh$.
--
--   This is the unfolding identity exhibiting the centre-folded kernel $K_f^{\mathrm{fold}}(x,y)=\sum_{\gamma}\int\xi(z)f(x^{-1}\gamma z y)\,dz$ as the kernel of the right convolution operator $R(f)$, tested against a bounded compactly supported $\Psi$ restricted to the truncation domain. It feeds the continuation of the spectral expansion of the automorphic kernel on the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B)
    (x : AdelicGL2 (𝓞 K) K) :
    ∫ y in AutomorphicForm.canonicalTruncationDomain K α β,
        (∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
                  ∫ z, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                    f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
                      (AutomorphicForm.centralScalar (𝓞 K) K z * y)) ∂νZK) * Ψ y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      convOp K f (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) x := by sorry
