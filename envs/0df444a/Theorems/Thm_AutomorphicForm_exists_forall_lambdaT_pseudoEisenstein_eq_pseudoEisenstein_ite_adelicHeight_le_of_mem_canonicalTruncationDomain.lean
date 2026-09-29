-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/96aa0734-39f0-5e62-8b34-b82eed25b126
-- title:
--   Truncated Eisenstein series as pseudo-Eisenstein series of the truncated section
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_F$ be a set of elements of $\mathrm{GL}_2$ of the adele ring of $F$. Write $\alpha_m$ for the homomorphism from the ideles to $\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring through $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and assume $\alpha_m(x)>0$ for all $x$. Then there exists $R_0\in\mathbb{R}$ such that for every $R\ge R_0$, every pair of characters $\mu,\nu$ of the idele group with $|\mu(x)|=|\nu(x)|=1$ for all $x$, every $s$ with $\operatorname{Re} s>1/2$, and every continuous $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for all $g$ and all $b$ in the Borel subgroup (lower-left entry zero), where $\chi_1=\mu\cdot\alpha_m^{\,s+1/2}$ and $\chi_2=\nu\cdot\alpha_m^{-(s+1/2)}$, the following holds for every $g$ in the canonical truncation domain `canonicalTruncationDomain F α β`. Let $H$ be the adelic height, $w$ the global Weyl element, $n(t)$ the upper unipotent matrix, $\nu_0$ the additive adelic Haar measure conditioned on the adelic box, and $E_\varphi(g')=\varphi(g')+\sum'_{\xi\in F}\varphi(w\,n(\xi)\,g')$. Then $$E_\varphi(g)-\mathbf 1_{H(g)>e^R}\cdot\big(\text{constant term of }E_\varphi\text{ along }t\mapsto n(t)\text{ against }\nu_0\big)(g)$$ equals $\varphi_R(g)+\sum'_{\xi\in F}\varphi_R(w\,n(\xi)\,g)$, where $\varphi_R(x)=\varphi(x)$ if $H(x)\le e^R$ and $\varphi_R(x)=-\mathrm{vol}(\text{box})^{-1}\int_{\mathbb{A}_F}\varphi(w^{-1}n(y)x)\,dy$ otherwise, the volume being that of the adelic box for the additive adelic Haar measure. The set $\Phi_F$, the principal-level-times-finite-part subgroups and the Hecke generators enter only as further fields of the carrier-pins record whose measure-theoretic fields supply $\nu_0$.
--
--   This is the rank-one case of Arthur's second formula for the truncated Eisenstein series, $\Lambda^T E(\varphi)=\sum_{\gamma\in B(F)\backslash G(F)}\varphi_T(\gamma g)$ with $\varphi_T=\varphi\mathbf 1_{H\le T}-M\varphi\mathbf 1_{H>T}$, here asserted on the canonical truncation domain of the determinant slab $\alpha\le\|\det g\|\le\beta$. It feeds the Maass–Selberg computations of inner products of truncated Eisenstein series over the slab.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lambdaT_pseudoEisenstein_eq_pseudoEisenstein_ite_adelicHeight_le_of_mem_canonicalTruncationDomain
    (F : Type) [Field F] [NumberField F]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦF : Set (AdelicGL2 (𝓞 F) F)) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : AutomorphicForm.IsInducedSection (𝓞 F) F
        (AutomorphicForm.etaFst μ αm hαm s) (AutomorphicForm.etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ),
    ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      @AutomorphicForm.lambdaT _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS _ _
        (productionPinsOf F ΦF (fun M => principalLevel (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).ν
        (fun t => AutomorphicForm.unipotentGL2 t)
        (NumberField.AdelicHeight.adelicHeight F) (Real.exp R)
        (AutomorphicForm.pseudoEisenstein F φ) g
      = AutomorphicForm.pseudoEisenstein F
          (fun x => if NumberField.AdelicHeight.adelicHeight F x ≤ Real.exp R then φ x
            else -(((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹ *
              AutomorphicForm.weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) φ x)) g := by sorry
