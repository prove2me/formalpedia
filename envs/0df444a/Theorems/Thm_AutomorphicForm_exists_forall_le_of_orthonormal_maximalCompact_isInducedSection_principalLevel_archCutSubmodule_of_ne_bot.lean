-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
-- name    : AutomorphicForm.exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/18866142-9acb-5627-b490-06a09973ae46
-- title:
--   Uniform bound on orthonormal systems of adelic induced sections
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal{O}_K$ with $N \neq \bot$, and $\mathrm{tysK}$ an archimedean type family for $K$, that is, for each infinite place $w$ a natural number $\mathrm{card}\,w$ together with data $\mathrm{rep}\,w\,i \in \mathrm{ArchRepAt}\,K\,w$ for $i < \mathrm{card}\,w$. Write $\alpha_m$ for the homomorphism from the idele units of $K$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring composed with the inclusion $\mathbb{R}_{\geq 0} \to \mathbb{R}$, the matrix group $\mathrm{GL}_2$ of the adele ring carrying its Borel measurable structure. The assertion is that there exists $D \in \mathbb{N}$ such that, for every proof that $\alpha_m$ takes strictly positive values, all homomorphisms $\mu, \nu$ from the idele units to $\mathbb{C}^\times$, all $s \in \mathbb{C}$, all $n \in \mathbb{N}$ and every family $\varphi : \mathrm{Fin}\,n \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ satisfying the following, one has $n \leq D$: each $\varphi_j$ is an induced section for the characters $\eta_1 = \mu \cdot \alpha_m^{s+1/2}$ and $\eta_2 = \nu \cdot \alpha_m^{-(s+1/2)}$, i.e. $\varphi_j(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_j(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower-left entry zero), where $\alpha_m^{t}(x) = ((\alpha_m x : \mathbb{R}) : \mathbb{C})^{t}$; each $\varphi_j$ is continuous; each $\varphi_j$ is invariant under right translation by elements of $\mathrm{principalLevel}\,(\mathcal{O}_K)\,K\,N$ (the level-one subgroup at $N$ intersected with its conjugate by the Weyl element) lying in the kernel of the archimedean projection $\mathrm{glArch}$; each $\varphi_j$ lies in $\bigsqcap_{w \mid \infty} \bigsqcup_{i < \mathrm{card}\,w} \mathrm{archTypeSubmoduleAt}\,K\,w\,(\mathrm{rep}\,w\,i)$; and the $\varphi_j$ are orthonormal for the Haar measure of the adelic maximal compact subgroup $\mathbf{K}$ of matrices whose finite part is integral and whose archimedean components are row isometries, $\int_{\mathbf{K}} \varphi_i(k)\overline{\varphi_j(k)}\,dk = \delta_{ij}$. The bound $D$ depends only on $K$, $N$ and $\mathrm{tysK}$, not on $\mu$, $\nu$ or $s$.
--
--   This is the uniform admissibility bound for the adelic principal series of $\mathrm{GL}_2$ over a number field: the number of mutually orthonormal induced sections of prescribed level $N$ and prescribed archimedean types is bounded independently of the inducing characters and of the complex parameter $s$. It feeds the finite-dimensionality statement [`AutomorphicForm.exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule), which turns this bound on orthonormal systems into a bound on the dimension of the space of restrictions to the maximal compact subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot.lean

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

theorem AutomorphicForm.exists_forall_le_of_orthonormal_maximalCompact_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∃ D : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (n : ℕ) (φ : Fin n → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : ∀ j, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ j))
      (_hφc : ∀ j, Continuous (φ j))
      (_hφlev : ∀ j (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ j (g * u) = φ j g)
      (_hφty : ∀ j, φ j ∈ archCutSubmodule K tysK)
      (_hφon : ∀ i j, ∫ k, φ i (k : AdelicGL2 (𝓞 K) K) * conj (φ j (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0),
      n ≤ D := by sorry
