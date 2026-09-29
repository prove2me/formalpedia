-- Prove2me | Theorems.Thm_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
-- name    : AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/7f0f7394-2587-5b49-83ed-6e28ec171c4f
-- title:
--   Cuspidality as orthogonality to all pseudo-Eisenstein series
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}$ and $\mathrm{GL}_2(\mathbb{A})$ written `AdelicGL2`. Let $d_1 < d_2$ be reals with $0 < d_1$, and let $\Phi \subseteq \mathrm{GL}_2(\mathbb{A})$ be contained in the determinant slab $\{g : \mathrm{ideleNorm}_F(\det g) \in [d_1,d_2]\}$, where `ideleNorm` is the module of the `distribHaarChar` of the idele, and be a fundamental domain for the range of $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb{A})$ acting on the Haar measure `adelicGLHaar` restricted to that slab. All further data are the `productionPinsOf` attached to $F$, $\Phi$, the level subgroups `levelOne`, the Hecke generators `heckeGen` and the box `adelicBox F`: the Borel $\sigma$-algebra `glBorel` and Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the domain $\Phi$, centre $Z = \top$ (all ideles), the Borel $\sigma$-algebra on $\mathbb{A}$, and the measure $\nu$ obtained by conditioning adelic additive Haar measure on `adelicBox F`. Let $\xi : Z \to \mathbb{C}^\times$ be a continuous character and let $f : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt` for these pins and $\xi$, i.e. the `LsXiMember` condition relative to the Haar measure, the domain $\Phi$, the centre and $\xi$. The assertion is an equivalence. The first statement is that, for Haar-almost every $g$, the constant term `constantTerm` of $f$ along the unipotent family $x \mapsto n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ — the integral of `constantTermIntegrand` against $\nu$ — vanishes at $g$. The second is that for every $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ which is an `IsSlabProfile` for $Z$ and $\xi$, that is: measurable, invariant under left multiplication by all $n(x)$ with $x \in \mathbb{A}$ and by the global points of the Borel subgroup, transforming by $\xi(z)$ under left multiplication by the central scalar of an idele $z \in Z$, bounded on every slab $\{d_1 \le \mathrm{ideleNorm}_F(\det g) \le d_2\}$ with $d_1 > 0$, and supported in a band $a \le \mathrm{adelicHeight}_F(g) \le b$ with $a > 0$, one has $\int_\Phi (\mathrm{pseudoEisenstein}\,\varphi)(g)\,\overline{f(g)}\,d\mu(g) = 0$, where $(\mathrm{pseudoEisenstein}\,\varphi)(g) = \varphi(g) + \sum_{\beta \in F}' \varphi(w\,n(\beta)\,g)$ with $w$ the adelic Weyl element.
--
--   This is the characterisation of the cuspidal part of the automorphic $L^2$ space of $\mathrm{GL}_2$, in the slab formulation used here, as the orthogonal complement of the span of the pseudo-Eisenstein series. It is invoked in the subsequent spectral decomposition statements, where the cuspidal and residual/continuous pieces of an automorphic function are separated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

theorem
AutomorphicForm.ae_constantTerm_eq_zero_iff_forall_setIntegral_pseudoEisenstein_mul_conj_eq_zero_slab
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (hξ : Continuous ξ)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ f) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
    (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
        constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).ν unipotentGL2 f g = 0) ↔
      ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, AutomorphicForm.IsSlabProfile F
          (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ →
        ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
            AutomorphicForm.pseudoEisenstein F φ g * starRingEnd ℂ (f g)
          ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ = 0 := by sorry
