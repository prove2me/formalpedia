-- Prove2me | Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
-- name    : AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/04f7b526-4cca-5a78-bb97-bfbcb18ddef5
-- title:
--   Automorphisation of a bounded compactly supported test function
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta\in\mathbb R$ satisfy $0<\alpha$ and $\alpha<\beta$. Fix a measurable structure on the idele class group $(\mathbb A_K)^\times$ that is Borel for its topology, a Haar measure $\nu_{Z}$ on $(\mathbb A_K)^\times$, and a monoid homomorphism $\xi_K$ from the full subgroup $\top\le(\mathbb A_K)^\times$ to $\mathbb C^\times$ such that $z\mapsto\xi_K(z)$ is continuous as a $\mathbb C$-valued function, $\xi_K$ is trivial on the image of $K^\times$ under the map induced by $K\to\mathbb A_K$, and $|\xi_K(z)|=1$ for all $z$. Let $\Psi:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be measurable, bounded in absolute value by some constant, and vanishing outside some compact set. Then the function
--   $$g\mapsto \sum^{\mathrm{f}}_{q\in \mathrm{GL}_2(K)/Z(\mathrm{GL}_2(K))}\ \int_{(\mathbb A_K)^\times}\xi_K(w)^{-1}\,\bigl(\mathbf 1_{\Phi_0}\Psi\bigr)\bigl(w\cdot(\iota(q.\mathrm{out})\,g)\bigr)\,d\nu_Z(w),$$
--   where $\iota$ is the map $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb A_K)$ induced by $K\to\mathbb A_K$, $w$ acts through the central scalar embedding, $q.\mathrm{out}$ is a chosen representative of the coset $q$, the sum is a finsum, and $\Phi_0$ is `canonicalTruncationDomain K α β` (the set component selected by a classical choice of a truncation datum for $K,\alpha,\beta$ when one exists, and $\emptyset$ otherwise), satisfies the predicate `IsAutomorphicFnAt` for $\xi_K$ at the pins `productionPinsOf` assembled from $\Phi_0$, the level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K` (the $M$-th principal level intersected with its Weyl conjugate, met with the kernel of the archimedean component map), the Hecke generators `heckeGen (𝓞 K) K v` at the finite places, and the adelic box `adelicBox K`; concretely, the predicate `LsXiMember` for the Borel structure `glBorel` and Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb A_K)$, the subgroup $\top\le(\mathbb A_K)^\times$ with character $\xi_K$, the domain $\Phi_0$, and this function.
--
--   This is the automorphisation (Poincaré-series) construction: averaging a bounded, compactly supported test function on $\mathrm{GL}_2(\mathbb A_K)$ over $\mathrm{GL}_2(K)$ modulo its centre against the character $\xi_K$ on the centre of the adelic group produces an element of the $\xi_K$-automorphic $L^2$ space cut out by the canonical truncation domain. It supplies the test vectors fed to the $L^2$ spectral decomposition and to the pairings with cusp forms, residues and Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain.lean

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

theorem AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (Ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hΨm : Measurable Ψ)
    (_hΨc : ∃ C : Set (AdelicGL2 (𝓞 K) K), IsCompact C ∧ ∀ y ∉ C, Ψ y = 0)
    (_hΨb : ∃ B : ℝ, ∀ y, ‖Ψ y‖ ≤ B) :
    letI := adeleBorel (𝓞 K) K
    IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK
      (fun g : AdelicGL2 (𝓞 K) K =>
          ∑ᶠ q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K),
            ∫ w, (((ξK ⟨w, Subgroup.mem_top w⟩)⁻¹ : ℂˣ) : ℂ) *
              (AutomorphicForm.canonicalTruncationDomain K α β).indicator Ψ
                (AutomorphicForm.centralScalar (𝓞 K) K w * (AutomorphicForm.globalPoints (𝓞 K) K q.out * g)) ∂νZK) := by sorry
