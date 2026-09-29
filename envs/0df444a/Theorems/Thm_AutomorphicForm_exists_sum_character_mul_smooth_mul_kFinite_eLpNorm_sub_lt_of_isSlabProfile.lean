-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile
-- name    : AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/24cfd2f0-34ce-550c-be53-7e64b7a46d52
-- title:
--   L² approximation of a slab profile by elementary tensors
-- statement:
--   Let $F$ be a number field, $\Phi$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and let the pin record be the one assembled from $\Phi$, the level-one subgroups $N \mapsto \mathrm{levelOne}$, the local Hecke generators $v \mapsto \mathrm{heckeGen}$ and the adelic box; its central group is all of $\mathbb{A}_F^\times$, so $\xi$ is a character $\mathbb{A}_F^\times \to \mathbb{C}^\times$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a slab profile for $\xi$: measurable, invariant under left translation by the unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x \in \mathbb{A}_F$, and by the image of the matrices in $\mathrm{GL}_2(F)$ with vanishing $(1,0)$ entry, satisfying $\varphi(z g) = \xi(z)\varphi(g)$ for central scalars $z$, bounded on each determinant slab $\|\det g\| \in [d_1,d_2]$ with $d_1 > 0$, and vanishing outside some adelic height band. Let $a,b$ with $0 < a$ satisfy: $\varphi(g) \neq 0$ implies the adelic height of $g$ lies in $[a,b]$; let $0 < a' < a$ and $b < b'$. Let $D \subseteq \mathbb{A}_F^\times$ be measurable and a fundamental domain for the principal ideles $F^\times$ with respect to idelic Haar measure, and let $\delta > 0$. Then there exist $n$ and data $\mu_j : \mathbb{A}_F^\times \to \mathbb{C}^\times$ ($j < n$), $h_j : \mathbb{R} \to \mathbb{C}$, $m_j : \mathbf{K} \to \mathbb{C}$, where $\mathbf{K}$ is the subgroup of elements whose finite part is integral and whose archimedean components are row isometries, such that each $\mu_j$ is a continuous unitary character trivial on $F^\times$; each $h_j$ is $C^\infty$, compactly supported and vanishes outside $[\log a', \log b']$; each $m_j$ is continuous, $\mathbf{K}$-finite (all right translates $k \mapsto m_j(k k_0)$ lie in one finite-dimensional subspace of $\mathbf{K} \to \mathbb{C}$) and right-invariant under the elements of $\mathbf{K}$ lying both in some neighbourhood $V$ of $1$ in $\mathrm{GL}_2(\mathbb{A}_F)$ and in the kernel of the archimedean projection; and the $L^2$ norm of $(t,k) \mapsto \varphi(\mathrm{diag}(t,1)\,k) - \sum_j \mu_j(t)\, h_j(\log \|t\|)\, m_j(k)$, with respect to the product of the idelic Haar measure restricted to $D$ and weighted by the density $\|t\|^{-1}$ with the Haar measure of $\mathbf{K}$, is less than $\delta$. Here $\|t\|$ is the module of $t$, the distributive Haar character of $\mathbb{A}_F$ at $t$.
--
--   This is the density statement underlying the spectral decomposition of a slab profile in Iwasawa coordinates $(t,k)$ on the torus times the maximal compact: functions of the form (idele class character) $\times$ (smooth bump in the logarithmic height) $\times$ ($\mathbf{K}$-finite function) approximate $\varphi$ arbitrarily well in $L^2$. It feeds the Paley–Wiener style estimate for slab profiles on the rational torus–unipotent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile
    (F : Type) [Field F] [NumberField F]
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (_hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
    (a b : ℝ) (_ha : 0 < a)
    (_hband : ∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b)
    (a' b' : ℝ) (_ha' : 0 < a') (_haa' : a' < a) (_hbb' : b < b')
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (_hDm : MeasurableSet D)
    (_hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (δ : ℝ) (_hδ : 0 < δ) :
    ∃ (n : ℕ) (μ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (h : Fin n → ℝ → ℂ)
      (m : Fin n → ↥(adelicMaximalCompact F) → ℂ),
      (∀ j, IsUnitaryChar (𝓞 F) F (μ j)) ∧ (∀ j, IsIdeleClassChar (𝓞 F) F (μ j)) ∧
      (∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ j x : ℂˣ) : ℂ)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ (j : Fin n) (u : ℝ), h j u ≠ 0 → u ∈ Set.Icc (Real.log a') (Real.log b')) ∧
      (∀ j, Continuous (m j)) ∧
      (∀ j, ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => m j (k * k₀)) ∈ W) ∧
      (∀ j, ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u : ↥(adelicMaximalCompact F)),
        (u : AdelicGL2 (𝓞 F) F) ∈ V → (u : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          m j (k * u) = m j k) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) -
            ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by sorry
