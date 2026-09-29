-- Prove2me | Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
-- name    : AutomorphicForm.isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/7d29b92a-0a93-588a-a194-d356c340627c
-- title:
--   From almost-everywhere to pointwise cuspidality and K_f-smoothness
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, and let $N$ be a nonzero ideal of $\mathcal{O}_K$. Throughout, the carrier pins are those produced by `productionPinsOf` from the data: the canonical truncation domain `canonicalTruncationDomain K α β` as domain $D$, the level groups $M \mapsto \mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and the adelic box as conditioning set; so the ambient measurable structure on $GL_2(\mathbb{A}_K)$ is the Borel one, $\mu$ is the Haar measure `adelicGLHaar`, the centre subgroup is $\top$, and $\nu$ is the additive adelic Haar measure on $\mathbb{A}_K$ conditioned on `adelicBox K`. Let $f\colon GL_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy: $f$ satisfies `IsAutomorphicFnAt` for these pins and $\xi_K$ (membership of `LsXiMember` for the Haar measure, the character $\xi_K$ on $\top$ and the truncation domain); $f$ is continuous; and $f(gu)=f(g)$ for all $g$ and all $u$ in the level group $\mathrm{principalLevel}(N)\sqcap \mathrm{finiteAdelicGL2Subgroup}$. The assertion is that if the constant term $g\mapsto \int f(n(a)g)\,d\nu(a)$ along the unipotent family $a \mapsto \begin{pmatrix}1&a\\0&1\end{pmatrix}$ vanishes for $\mu$-almost every $g$, then $f$ satisfies `IsSmoothCuspAutomorphicFnAt` for these pins and $\xi_K$: it is automorphic as above, its constant term vanishes at every $g$, and it is $K_f$-smooth, i.e. the stabiliser of $f$ in $\mathrm{finiteAdelicGL2Subgroup}$ (the kernel of the archimedean projection) acting by right translation is open.
--
--   This is the standard upgrade of cuspidality from an almost-everywhere statement to a pointwise one for a continuous automorphic function, together with the observation that invariance under a principal level group gives smoothness for the finite-adelic maximal compact. It is used in the one-term wave-packet representation of pseudo-Eisenstein series minus their residual projection, where duality against pseudo-Eisenstein series only yields vanishing of the constant term almost everywhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero.lean

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
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isSmoothCuspAutomorphicFnAt_of_continuous_of_principalLevel_of_ae_constantTerm_eq_zero
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (_hf : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f)
    (_hfc : Continuous f)
    (_hflev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, f (g * u) = f g) :
    letI := adeleBorel (𝓞 K) K
    ∀ (_hct : ∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K),
        constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 f g = 0),
    IsSmoothCuspAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK f := by sorry
