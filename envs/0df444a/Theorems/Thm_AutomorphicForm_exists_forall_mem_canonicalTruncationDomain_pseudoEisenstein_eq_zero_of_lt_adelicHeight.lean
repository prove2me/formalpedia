-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
-- name    : AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/0e30b4d3-d806-5126-bedf-8625afd6f8b8
-- title:
--   High-height vanishing of the pseudo-Eisenstein series of a slab profile
-- statement:
--   Let $K$ be a number field, $\alpha,\beta$ real numbers with $0<\alpha$ and $\alpha<\beta$, let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy `IsSlabProfile`, i.e. $\varphi$ is measurable (for the Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$), satisfies $\varphi(n(x)g)=\varphi(g)$ for every adele $x$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, satisfies $\varphi(\gamma g)=\varphi(g)$ for every $\gamma\in \mathrm{GL}_2(K)$ with vanishing lower-left entry (embedded adelically), transforms by $\varphi(zg)=\xi_K(z)\varphi(g)$ under central scalars $z\in(\mathbb{A}_K)^\times$, is bounded on each determinant slab $\{g:\ \|\det g\|\in[d_1,d_2]\}$ with $d_1>0$, and has a height band: there are $a,b$ with $a>0$ such that $\varphi(g)\neq0$ forces the adelic height $H(g)=\prod_{v\mid\infty}(\cdot)^{m_v}\cdot\prod_{v\nmid\infty}(\cdot)$ to lie in $[a,b]$. Then there exists $T\in\mathbb{R}$ such that for every $g$ in the canonical truncation domain attached to $(\alpha,\beta)$ — the second set component of a chosen witness of `IsTruncationDatum` for $K,\alpha,\beta$, and $\emptyset$ if none exists — with $H(g)>T$ one has $\varphi(g)+\sum_{\beta'\in K}\varphi\bigl(w\,n(\beta')\,g\bigr)=0$, $w$ being the adelic image of the Weyl element.
--
--   This is the support statement for pseudo-Eisenstein series in height form: a slab profile supported in a height band produces a pseudo-Eisenstein series vanishing above a fixed height. It feeds the inner-product and integrability estimates for pseudo-Eisenstein series used in the spectral side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight.lean

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

theorem AutomorphicForm.exists_forall_mem_canonicalTruncationDomain_pseudoEisenstein_eq_zero_of_lt_adelicHeight
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK φ) :
    ∃ T : ℝ, ∀ g ∈ AutomorphicForm.canonicalTruncationDomain K α β,
      T < NumberField.AdelicHeight.adelicHeight K g →
        AutomorphicForm.pseudoEisenstein K φ g = 0 := by sorry
