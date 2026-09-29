-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
-- name    : AutomorphicForm.isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8c19fabe-2fbe-55af-81dc-d5181cf238fc
-- title:
--   Right convolution preserves induced sections with level and type
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$, and $\mathrm{tysK}$ an archimedean type family for $K$, i.e. a function assigning to each infinite place $w$ a cardinality $\mathrm{card}(w) \in \mathbb{N}$ together with representations $\mathrm{rep}(w, i) \in \mathrm{ArchRepAt}(K, w)$ for $i \in \mathrm{Fin}(\mathrm{card}(w))$. Let $\chi_1, \chi_2 \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ be monoid homomorphisms and let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and an induced section for $(\chi_1,\chi_2)$, meaning $\varphi(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero), where $b_{00}, b_{11}$ are the diagonal entries viewed as units. Let $f \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support, factorizable in the sense that $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for an archimedean test factor $f_\infty$ and a finite test factor $f_{\mathrm{fin}}$, bi-invariant under $U_N = \mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$ (i.e. $f(ug) = f(g)$ and $f(gu) = f(g)$ for $u \in U_N$), and archimedean bi-finite of type $\mathrm{tysK}$, i.e. $x \mapsto f(x^{-1})$ lies in $\mathrm{archCutSubmodule}(K,\mathrm{tysK}) = \bigsqcap_w \bigsqcup_i \mathrm{archTypeSubmoduleAt}(K, w, \mathrm{rep}(w,i))$ and $f$ lies in $\mathrm{archDualCutSubmodule}(K,\mathrm{tysK})$. Then, with the Borel measurable structures on $\mathbb{A}_K$ and on $\mathrm{GL}_2(\mathbb{A}_K)$, the right convolution $(\mathrm{rightConv}\,\varphi\,f)(g) = \int \varphi(gx) f(x)\,d\mu(x)$ against the adelic Haar measure satisfies: it is again an induced section for $(\chi_1,\chi_2)$; it is continuous; it is archimedean $K$-finite, i.e. at every infinite place $w$ its right translates under $\mathrm{archRowIsometrySubgroup}(K,w)$ satisfy $\mathrm{RightTranslatesSpanFinite}$; it is right $U_N$-invariant, $(\mathrm{rightConv}\,\varphi\,f)(gu) = (\mathrm{rightConv}\,\varphi\,f)(g)$ for all $g$ and all $u \in U_N$; and it lies in $\mathrm{archCutSubmodule}(K,\mathrm{tysK})$.
--
--   This is the stability statement for the action of the adelic Hecke algebra by right convolution on a principal-series induced space: convolving a continuous induced section by a factorizable, level-$N$ bi-invariant, archimedean bi-finite test function again produces a continuous induced section of the same central characters, of level $N$, archimedean $K$-finite, and of prescribed archimedean type. It supplies the hypothesis on the convolved section in the subsequent expansion of an integral of $\varphi \cdot \overline{\mathrm{rightConv}\,\varphi\,f}$ as a sum over an orthonormal family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite.lean

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

theorem AutomorphicForm.isInducedSection_rightConv_and_continuous_and_isArchKFinite_and_principalLevel_and_mem_archCutSubmodule_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K)
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (_hφc : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfF : IsFactorizableTestFn K f)
    (_hfbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_hfty : IsArchBiFinite K tysK f) :
    letI := adeleBorel (𝓞 K) K
    IsInducedSection (𝓞 K) K χ₁ χ₂ (rightConv K φ f) ∧
    Continuous (rightConv K φ f) ∧
    IsArchKFinite K (rightConv K φ f) ∧
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, rightConv K φ f (g * u) = rightConv K φ f g) ∧
    rightConv K φ f ∈ archCutSubmodule K tysK := by sorry
