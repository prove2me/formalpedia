-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
-- name    : AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8ad560a0-1c2e-5c64-a4d4-7eaaf21c1cef
-- title:
--   L² approximation of band-supported invariant functions by elementary tensors
-- statement:
--   Let $F$ be a number field and let $a',b',a_1,b_1$ be reals with $0<a'<a_1$ and $b_1<b'$. Write $\mathbf{K}=$ `adelicMaximalCompact F` for the subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ of matrices whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place $w$ is a row isometry (determinant of norm $1$, and the two rows act isometrically for the sum-of-squares form), and $\|t\|=$ `ideleNorm F t`, the value at $t$ of the distributive Haar character of $\mathbb{A}_F$. Let $G:\mathbb{A}_F^\times\times\mathbf{K}\to\mathbb{C}$ be continuous, invariant in the first variable under the subgroup of principal ideles (the image of $F^\times$), and such that $G(t,k)\neq 0$ forces $\|t\|\in[a_1,b_1]$. Let $D\subseteq\mathbb{A}_F^\times$ be a measurable fundamental domain for the principal ideles acting on the Haar measure `idelicHaar F`, and let $\delta>0$. Then there exist $n\in\mathbb{N}$ and families $\mu_j:\mathbb{A}_F^\times\to\mathbb{C}^\times$ ($j<n$) of monoid homomorphisms, $h_j:\mathbb{R}\to\mathbb{C}$ and $m_j:\mathbf{K}\to\mathbb{C}$ such that: each $\mu_j$ has $|\mu_j(x)|=1$ for all $x$, is trivial on the image of $F^\times$, and is continuous as a $\mathbb{C}$-valued function; each $h_j$ is $C^\infty$ on $\mathbb{R}$, has compact support, and vanishes outside $[\log a',\log b']$; each $m_j$ is continuous, right $\mathbf{K}$-finite in the sense that some finite-dimensional $\mathbb{C}$-subspace $W$ of functions $\mathbf{K}\to\mathbb{C}$ contains every translate $k\mapsto m_j(kk_0)$, and smooth at the finite places in the sense that for some neighbourhood $V$ of $1$ in $\mathrm{GL}_2(\mathbb{A}_F)$ one has $m_j(ku)=m_j(k)$ for all $k$ and all $u\in V$ lying in the kernel of the archimedean projection `glArch`; and, finally, the difference $G(t,k)-\sum_j \mu_j(t)\,h_j(\log\|t\|)\,m_j(k)$ is almost everywhere strongly measurable and has $L^2$ norm less than $\delta$ for the product of the measure $\|t\|^{-1}\,d t$ on $D$ (the restriction of `idelicHaar F` to $D$, with density $\mathrm{ofReal}(\|t\|^{-1})$) with the Haar measure `maximalCompactHaar F` on $\mathbf{K}$.
--
--   This is the $L^2$ form of the density of elementary tensors — unitary idele class character times smooth bump in $\log\|t\|$ times $\mathbf{K}$-finite function — in the space of continuous, $F^\times$-invariant functions supported in a norm band, with the band widened from $[a_1,b_1]$ to $[\log a',\log b']$ in the bump variable. It is used by [`AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile`](thm.html#AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_isSlabProfile), and is obtained from the corresponding uniform (sup-norm) approximation together with the finiteness of the measure of the band.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported.lean

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

theorem AutomorphicForm.exists_sum_character_mul_smooth_mul_kFinite_eLpNorm_sub_lt_of_continuous_invariant_bandSupported
    (F : Type) [Field F] [NumberField F]
    (a' b' a₁ b₁ : ℝ) (ha' : 0 < a') (ha₁ : a' < a₁) (hb₁ : b₁ < b')
    (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (hGc : Continuous G)
    (hGinv : ∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p)
    (hGsupp : ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁)
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (δ : ℝ) (hδ : 0 < δ) :
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
      AEStronglyMeasurable (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2)
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) => G p - ∑ j, ((μ j p.1 : ℂˣ) : ℂ) * h j (Real.log (NumberField.TateGlobal.ideleNorm F p.1)) * m j p.2) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by sorry
