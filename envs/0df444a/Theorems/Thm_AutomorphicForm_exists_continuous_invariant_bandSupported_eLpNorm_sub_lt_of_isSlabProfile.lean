-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
-- name    : AutomorphicForm.exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/5499a245-a9f5-5342-93ce-4959af0a56a2
-- title:
--   L² approximation of a slab profile by continuous band-supported functions
-- statement:
--   Let $F$ be a number field, $\Phi$ a set of adelic $2\times 2$ invertible matrices (entering only as the distinguished-set datum of the pins package `productionPinsOf`, whose central subgroup component is all of $(\mathbb{A}_F)^\times$), and $\xi$ a character of that full group of ideles. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy `IsSlabProfile`: $\varphi$ is measurable, invariant under left translation by unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $x\in\mathbb{A}_F$, and by the images of matrices in $\mathrm{GL}_2(F)$ with vanishing $(1,0)$-entry, satisfies $\varphi(zg)=\xi(z)\varphi(g)$ for central scalars $z$, is bounded on each slab $\{\,\|\det g\|\in[d_1,d_2]\,\}$ with $d_1>0$, and vanishes outside some height band. Assume moreover $0<a$ and $\varphi(g)\neq 0\Rightarrow \mathrm{adelicHeight}_F(g)\in[a,b]$, and let $0<a'<a$, $b<b'$. Let $D$ be a measurable fundamental domain for the subgroup of principal ideles acting on $(\mathbb{A}_F)^\times$ with respect to the Haar measure `idelicHaar`, and let $\rho_D$ be the product of $\|t\|^{-1}$ times that Haar measure restricted to $D$ with the Haar measure of the maximal compact subgroup $\mathbf{K}$ (matrices with integral finite part and row-isometric archimedean components). Then for every $\delta>0$ there exist a continuous $G:(\mathbb{A}_F)^\times\times\mathbf{K}\to\mathbb{C}$ and reals $a'<a_1$, $b_1<b'$ such that $G(\gamma t,k)=G(t,k)$ for all principal ideles $\gamma$, $G$ vanishes wherever $\|t\|\notin[a_1,b_1]$, the function $(t,k)\mapsto \varphi(\mathrm{diag}(t,1)\,k)-G(t,k)$ is a.e. strongly measurable for $\rho_D$, and its $L^2(\rho_D)$-norm is less than $\delta$.
--
--   This is the approximation step that replaces a slab profile, viewed through the Iwasawa-type coordinates $(t,k)\mapsto \mathrm{diag}(t,1)k$, by a continuous function on $(\mathbb{A}_F^\times/F^\times)\times\mathbf{K}$ supported in a slightly enlarged norm band, at the cost of an arbitrarily small $L^2$ error. It feeds the subsequent decomposition of such a profile into sums of characters times smooth $\mathbf{K}$-finite functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile.lean

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

theorem AutomorphicForm.exists_continuous_invariant_bandSupported_eLpNorm_sub_lt_of_isSlabProfile
    (F : Type) [Field F] [NumberField F]
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : AutomorphicForm.IsSlabProfile F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ)
    (a b : ℝ) (ha : 0 < a)
    (hband : ∀ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b)
    (a' b' : ℝ) (ha' : 0 < a') (haa' : a' < a) (hbb' : b < b')
    (D : Set (AdeleRing (𝓞 F) F)ˣ) (hDm : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D (NumberField.Idele.idelicHaar F))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (G : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) → ℂ) (a₁ b₁ : ℝ),
      Continuous G ∧ a' < a₁ ∧ b₁ < b' ∧
      (∀ γ ∈ M4aHerbrand.principalIdeles (𝓞 F) F, ∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G (γ * p.1, p.2) = G p) ∧
      (∀ p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F), G p ≠ 0 → NumberField.TateGlobal.ideleNorm F p.1 ∈ Set.Icc a₁ b₁) ∧
      AEStronglyMeasurable (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) - G p)
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) ∧
      eLpNorm (fun p : (AdeleRing (𝓞 F) F)ˣ × ↥(adelicMaximalCompact F) =>
          φ (NumberField.AdelicLevel.diagOne p.1 * (p.2 : AdelicGL2 (𝓞 F) F)) - G p) 2
        ((((NumberField.Idele.idelicHaar F).restrict D).withDensity
            (fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm F t)⁻¹))).prod
          (maximalCompactHaar F)) < ENNReal.ofReal δ := by sorry
