-- Prove2me | Theorems.Thm_AutomorphicForm_ae_constantTerm_eq_zero_of_ae_eq_restrict_slab
-- name    : AutomorphicForm.ae_constantTerm_eq_zero_of_ae_eq_restrict_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/aaddd7e7-803c-5918-a746-c7011ddf7108
-- title:
--   A.e. vanishing of the constant term is an L²-class invariant
-- statement:
--   Let $F$ be a number field, let $d_1<d_2$ be reals with $0<d_1$, and let $\Phi$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`) contained in the determinant slab $\{g : \|\det g\| \in [d_1,d_2]\}$, where $\|\cdot\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the modulus `distribHaarChar` of an idele acting on the adele ring; assume $\Phi$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` (entrywise $F \to \mathbb{A}_F$) on the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` restricted to that slab. Fix the data `productionPinsOf F Φ (levelOne) (heckeGen) (adelicBox F)`: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the set $\Phi$, the subgroup $\top$ of $\mathbb{A}_F^\times$, the level subgroups `levelOne`, the Hecke elements `heckeGen`, and the measure $\nu$ on $\mathbb{A}_F$ obtained by conditioning additive adelic Haar measure on `adelicBox F`. Let $\xi : \top \to \mathbb{C}^\times$ be a homomorphism and $v_1,v_2 : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ both satisfy `IsAutomorphicFnAt` for these data and $\xi$. If $v_1 = v_2$ almost everywhere for Haar measure restricted to $\Phi$, and if for Haar-almost every $g$ the constant term $\int v_1(u(q)g)\,d\nu(q)$ along $u(q)=\begin{pmatrix}1&q\\0&1\end{pmatrix}$ vanishes, then the same constant term of $v_2$ vanishes for Haar-almost every $g$.
--
--   This is a class-invariance statement for the cuspidality condition in the spectral analysis of the automorphic $L^2$ space of $\mathrm{GL}_2$ over a number field: almost everywhere vanishing of the unipotent constant term depends only on the class of an automorphic function modulo null sets of the fundamental domain inside a determinant slab. It is used in the equivalence between this vanishing and the orthogonality of the function to all pseudo-Eisenstein series over the slab.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ae_constantTerm_eq_zero_of_ae_eq_restrict_slab.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
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

theorem AutomorphicForm.ae_constantTerm_eq_zero_of_ae_eq_restrict_slab
    (F : Type) [Field F] [NumberField F]
    (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
    (Φ : Set (AdelicGL2 (𝓞 F) F))
    (_hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
    (_hΦ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict {g | NumberField.TateGlobal.ideleNorm F
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
    (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (v₁ v₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (_h₁ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ v₁)
    (_h₂ : IsAutomorphicFnAt F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ v₂)
    (_h₁₂ : v₁ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 F) F).restrict Φ] v₂)
    (_hc₁ :
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
      letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
      (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
          constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)).ν unipotentGL2 v₁ g = 0)) :
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).mS
    letI := (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).nS
    (∀ᵐ g ∂(productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).μ,
        constantTerm (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)).ν unipotentGL2 v₂ g = 0) := by sorry
