-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight
-- name    : AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/da63c2b3-6737-5f03-a0c5-1569ed4960aa
-- title:
--   Vanishing of automorphised compactly supported functions above a height
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$; write $\mathbb{A}$ for the adele ring of $K$ and $\mathrm{AdelicGL2}$ for $\mathrm{GL}_2(\mathbb{A})$, equipped with its Borel $\sigma$-algebra, the group $\mathbb{A}^\times$ of units carrying a measurable space structure. Given an arbitrary measure $\nu_{Z}$ on $\mathbb{A}^\times$, an arbitrary homomorphism $\xi$ from the full subgroup $\top \le \mathbb{A}^\times$ to $\mathbb{C}^\times$, and a function $\Psi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ for which there exists a compact set $C$ with $\Psi$ vanishing off $C$, the assertion is that there exists a real number $T$ such that for every $g$ in the canonical truncation domain $\Phi_0 = \Phi_0(K,\alpha,\beta)$ (the second set-component of the classically chosen truncation datum for $K,\alpha,\beta$, or $\emptyset$ if no such datum exists) with $T < \mathrm{adelicHeight}\,K\,g$ — the height being the product of the archimedean height of the archimedean component of $g$ with the finite height of its finite component — the finite sum over cosets $q \in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))$ of $$\int_{\mathbb{A}^\times} \xi(w)^{-1}\,\bigl(\mathbf{1}_{\Phi_0}\Psi\bigr)\bigl(z(w)\cdot(\iota(q_{\mathrm{out}})\, g)\bigr)\,d\nu_{Z}(w)$$ vanishes, where $z$ sends an idele to the corresponding scalar matrix, $\iota$ is the map $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A})$ induced by $K \to \mathbb{A}$, and $q_{\mathrm{out}}$ is a chosen representative of the coset $q$.
--
--   This is the height form of the statement that the automorphisation (Poincaré-type series) of a compactly supported function on $\mathrm{GL}_2(\mathbb{A})$ has support bounded in the height direction on the truncation domain, a consequence of reduction theory for $\mathrm{GL}_2$. It is used in the analysis of the continuous spectrum, where pairings of such automorphisations against Eisenstein series must be shown to converge and to be controlled in $L^2$ of the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight.lean

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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_finsum_integral_indicator_eq_zero_of_lt_adelicHeight
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0) :
    ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      T < NumberField.AdelicHeight.adelicHeight K g →
        (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) g = 0 := by sorry
