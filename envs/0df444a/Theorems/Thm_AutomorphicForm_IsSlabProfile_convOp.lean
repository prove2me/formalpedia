-- Prove2me | Theorems.Thm_AutomorphicForm_IsSlabProfile_convOp
-- name    : AutomorphicForm.IsSlabProfile.convOp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/7dd948bd-e258-5f17-bf00-1ab98a4e3c4c
-- title:
--   Right convolution by a test function preserves slab profiles
-- statement:
--   Let $K$ be a number field, let $Z$ be the full group $(\mathbb{A}_K^\times)$ of units of the adele ring, viewed as the top subgroup, and let $\xi_K : Z \to \mathbb{C}^\times$ be a group homomorphism. Let $\psi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `IsSlabProfile`, i.e. (i) $\psi$ is measurable for the Borel structure on $\mathrm{GL}_2(\mathbb{A}_K)$; (ii) $\psi(u(x)g) = \psi(g)$ for every adele $x$, where $u(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; (iii) $\psi(\gamma g) = \psi(g)$ for every $\gamma \in \mathrm{GL}_2(K)$ with vanishing lower-left entry, embedded by the map induced by $K \to \mathbb{A}_K$; (iv) $\psi(zI\,g) = \xi_K(z)\psi(g)$ for every idele unit $z$; (v) for all reals $d_1 > 0$, $d_2$ there is $C$ with $\|\psi(g)\| \le C$ whenever the idele norm (the scaling factor of Haar measure) of $\det g$ lies in $[d_1,d_2]$; (vi) there are $a > 0$ and $b$ such that $\psi(g) \ne 0$ forces the adelic height $H(g)$, the product of its archimedean and finite parts, to lie in $[a,b]$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support. Then the right convolution $\mathrm{convOp}\,f\,\psi : g \mapsto \int \psi(gx) f(x)\,dx$, taken against the chosen Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, again satisfies all six conditions with the same $\xi_K$.
--
--   This is the statement that the space of slab profiles on $\mathrm{GL}_2(\mathbb{A}_K)$ with fixed central character is stable under the right regular action of the convolution algebra of continuous compactly supported functions. It is used in the transport of a Paley–Wiener datum under right convolution, namely by [`AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite`](thm.html#AutomorphicForm.paleyWiener_convOp_and_convOp_pseudoEisenstein_eq_pseudoEisenstein_convOp_of_isArchBiFinite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsSlabProfile_convOp.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.IsSlabProfile.convOp
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ) (_hψ : AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK ψ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f) :
    AutomorphicForm.IsSlabProfile K (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) ξK (convOp K f ψ) := by sorry
