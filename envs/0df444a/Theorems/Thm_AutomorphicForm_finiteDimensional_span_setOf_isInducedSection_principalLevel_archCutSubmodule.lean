-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule
-- name    : AutomorphicForm.finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/546f873f-df61-585b-9c07-7fd3515e67ce
-- title:
--   Finite-dimensionality of K-finite induced sections at principal level
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$ and adele ring $\mathbb A$, let $N$ be a nonzero ideal of $\mathcal O_K$, let `tysK` be an `ArchTypeFamily` for $K$ (for each infinite place $w$ a natural number $\mathrm{card}(w)$ together with, for each $i < \mathrm{card}(w)$, a finite-dimensional complex representation of the row-isometry subgroup of $\mathrm{GL}_2$ of the completion at $w$), and let $\mu,\nu\colon\mathbb A^\times\to\mathbb C^\times$ be multiplicative characters. Put $\alpha_m\colon\mathbb A^\times\to\mathbb R^\times$ for the idelic modulus, namely the distributive Haar character of $\mathbb A$ viewed in $\mathbb R_{\ge 0}$ and then in $\mathbb R^\times$, the adele ring carrying its Borel $\sigma$-algebra. Then for every proof that $\alpha_m(x)>0$ for all $x$, and every $s\in\mathbb C$, the complex span of the set of functions $\varphi\colon \mathrm{GL}_2(\mathbb A)\to\mathbb C$ satisfying all of: (i) $\varphi(bg)=\chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$ for all $g$ and all $b$ in the subgroup of matrices with vanishing lower-left entry, where $\chi_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\chi_2=\nu\cdot\alpha_m^{-(s+1/2)}$ (complex powers of the positive real $\alpha_m$); (ii) $\varphi$ continuous; (iii) at every infinite place $w$, the right translates of $\varphi$ by the archimedean row-isometry subgroup at $w$ span a finite-dimensional space; (iv) $\varphi(gu)=\varphi(g)$ for all $g$ and all $u$ in the intersection of the principal level-$N$ subgroup with the kernel of the archimedean projection; (v) $\varphi$ lies in the submodule cut out by `tysK`, i.e. in $\bigsqcap_w \bigsqcup_{i<\mathrm{card}(w)}$ of the corresponding archimedean type submodules; is finite-dimensional over $\mathbb C$.
--
--   This is the admissibility statement for the adelic principal series restricted to a principal congruence level: the multiplicity of a fixed finite family of archimedean types in sections induced from the Borel subgroup, with prescribed level-$N$ invariance, is finite. It is the finiteness input for constructing a countable orthonormal family of flat induced sections at principal congruence level, used on the Eisenstein side of the spectral decomposition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.finiteDimensional_span_setOf_isInducedSection_principalLevel_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K)
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)) (s : ℂ),
    FiniteDimensional ℂ ↥(Submodule.span ℂ {φ : AdelicGL2 (𝓞 K) K → ℂ |
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ ∧
        Continuous φ ∧ IsArchKFinite K φ ∧
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) ∧
        φ ∈ archCutSubmodule K tysK}) := by sorry
