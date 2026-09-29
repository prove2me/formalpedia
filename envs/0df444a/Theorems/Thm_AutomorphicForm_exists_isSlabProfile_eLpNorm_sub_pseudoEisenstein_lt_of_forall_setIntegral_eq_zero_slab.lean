-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
-- name    : AutomorphicForm.exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/64873958-80e6-5d6d-8e80-062bef7cece9
-- title:
--   Pseudo-Eisenstein approximation in the orthogonal complement of cusp forms
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}$ and $\mathrm{GL}_2(\mathbb{A})$ carried by `AdelicGL2`, let $0 < d_1 < d_2$ be reals, and let $\Phi \subseteq \mathrm{GL}_2(\mathbb{A})$ be contained in the determinant slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is the idele norm given by the modulus of the distributive Haar character, and be a fundamental domain for the image of $\mathrm{GL}_2(F)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to that slab. Write `pins` for the production carrier data attached to $\Phi$, the level subgroups $N \mapsto$ `levelOne`, the Hecke generators $v \mapsto$ `heckeGen` and the adelic box: its measurable structure is the Borel one, its measure $\mu$ is `adelicGLHaar`, its region $D$ is $\Phi$, its central subgroup $Z$ is all of $\mathbb{A}^\times$, and its auxiliary measure $\nu$ is additive adelic Haar measure conditioned on `adelicBox`. Let $\xi : Z \to \mathbb{C}^\times$ be a continuous character, and let $f_e : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt` for these data and $\xi$, that is the predicate `LsXiMember` for the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the region $\Phi$, the subgroup $Z$ and $\xi$ (membership in the $\xi$-equivariant $L^2$ space on $\Phi$). Assume further that $f_e$ is orthogonal to all cuspidal vectors: for every $u : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ satisfying the same predicate `IsAutomorphicFnAt` with character $\xi$ and such that, for $\mu$-almost every $g$, the constant term `constantTerm` of $u$ at $g$ along the unipotent family $x \mapsto \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ integrated against $\nu$ vanishes, one has $\int_\Phi f_e(g)\overline{u(g)}\,d\mu(g) = 0$. Then for every $\varepsilon > 0$ there is $\varphi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ which is a slab profile for $Z$ and $\xi$ in the sense of `IsSlabProfile`, namely $\varphi$ is measurable, invariant under left multiplication by $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ for every adelic $x$ and by `globalPoints` $\gamma$ for every $\gamma$ in the rational Borel subgroup, satisfies $\varphi(\mathrm{diag}(z,z)g) = \xi(z)\varphi(g)$ for $z \in Z$, is bounded on every slab $\{d_1' \le \|\det\| \le d_2'\}$ with $d_1' > 0$, and vanishes outside a band $a \le$ `adelicHeight` $\le b$ with $a > 0$; and such that the $L^2$ norm `eLpNorm` of $f_e -$ `pseudoEisenstein` $\varphi$ with respect to $\mu$ restricted to $\Phi$ is less than $\varepsilon$, where `pseudoEisenstein` $\varphi$ sends $g$ to $\varphi(g) + \sum_{\beta \in F} \varphi\big(w\,\begin{pmatrix} 1 & \beta \\ 0 & 1\end{pmatrix} g\big)$ with $w$ the adelic Weyl element.
--
--   This is the density statement for pseudo-Eisenstein (incomplete theta) series: on the determinant slab, the closure of the space of pseudo-Eisenstein series of slab profiles exhausts the orthogonal complement of the functions with almost everywhere vanishing constant term, so that a vector orthogonal to all such cuspidal vectors is approximated in $L^2(\Phi)$ by a single pseudo-Eisenstein series. It feeds the characterisation of almost everywhere vanishing of the constant term by orthogonality to pseudo-Eisenstein series, and the construction of matched Paley–Wiener data in the spectral decomposition on adelic $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab.lean

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
AutomorphicForm.exists_isSlabProfile_eLpNorm_sub_pseudoEisenstein_lt_of_forall_setIntegral_eq_zero_slab
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (hξ : Continuous ξ)
    (fe : AdelicGL2 (𝓞 F) F → ℂ)
    (_hfe : IsAutomorphicFnAt F
      (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ fe)
    (_hperp :
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
      ∀ u : AdelicGL2 (𝓞 F) F → ℂ,
        IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ u →
        (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
            constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
                (adelicBox F)).ν unipotentGL2 u g = 0) →
        ∫ g in (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D,
            fe g * starRingEnd ℂ (u g)
          ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ = 0)
    (ε : ℝ) (_hε : 0 < ε) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    ∃ φ : AdelicGL2 (𝓞 F) F → ℂ, AutomorphicForm.IsSlabProfile F
        (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ φ ∧
      eLpNorm (fe - AutomorphicForm.pseudoEisenstein F φ) 2 ((productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ.restrict (productionPinsOf F Φ (fun N => levelOne (𝓞 F)
          F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).D) < ENNReal.ofReal ε := by sorry
