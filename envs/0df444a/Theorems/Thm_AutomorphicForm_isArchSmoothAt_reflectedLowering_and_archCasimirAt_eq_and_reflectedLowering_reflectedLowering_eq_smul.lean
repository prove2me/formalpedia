-- Prove2me | Theorems.Thm_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
-- name    : AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/47321fd9-9e75-592e-8272-b687b1deaec8
-- title:
--   Reflected lowering operator: weight one, Casimir eigenvalue, T²=1-4λ
-- statement:
--   Let $F$ be a number field and $w$ a real infinite place of $F$ (hypothesis $hw$). All functions are complex-valued functions on `AdelicGL2 (𝓞 F) F`, the group $\mathrm{GL}_2$ over the adele ring of $F$. Let $T$ be an operator on such functions, assumed (hypothesis $hT$) to be given by $(T\theta)(g) = \bigl(D_H\theta - i\,(D_E\theta + D_{F^-}\theta)\bigr)\bigl(g\cdot \mathrm{archRealGLAt}\,hw\,J\bigr)$, where $J$ is Mathlib's reflection `UpperHalfPlane.J` in $\mathrm{GL}_2(\mathbb{R})$ placed at $w$ through the monoid homomorphism `archRealGLAt hw`, and where $D_d\theta(g) = \frac{d}{dt}\theta(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)\big|_{t=0}$ is the derivative along the one-parameter family `archFlowMatrix d t` at $w$, for $d$ one of the three directions `H`, `E`, `Fm`. Let $\varphi$ satisfy `IsArchSmoothAt hw φ`: for every $g$, the function $e \mapsto \varphi(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ on $2\times 2$ real matrices is $C^\infty$ on the set of matrices of nonzero determinant. Write $\Omega\varphi = -\bigl(\tfrac14 D_H D_H\varphi - \tfrac12 D_H\varphi + D_E D_{F^-}\varphi\bigr)$ for `archCasimirAt hw`, and let weight one mean the predicate `HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ`, i.e. that $\varphi$ transforms at $w$ under the character `archWeightCharAt hw 1`, the first power of the weight-one character `archWeightOneAt hw` obtained from `archWeightOneℝ` by transport along the isomorphism $F_w \cong \mathbb{R}$. Then five assertions hold simultaneously: (1) if $\varphi$ has weight one at $w$ then $D_E\varphi - D_{F^-}\varphi = i\,\varphi$; (2) $T\varphi$ again satisfies `IsArchSmoothAt hw`; (3) if $\varphi$ has weight one at $w$, so does $T\varphi$; (4) for every $\lambda \in \mathbb{C}$, if $\Omega\varphi = \lambda\varphi$ then $\Omega(T\varphi) = \lambda\,T\varphi$; (5) for every $\lambda \in \mathbb{C}$, if $\Omega\varphi = \lambda\varphi$ and $\varphi$ has weight one at $w$, then $T(T\varphi) = (1-4\lambda)\,\varphi$.
--
--   This is the archimedean $(\mathfrak{g},K)$-calculus at a real place: the lowering operator composed with right translation by the reflection acts on the space of smooth weight-one functions with a fixed Casimir eigenvalue, and squares to multiplication by $1-4\lambda$ there. It is used for the weight-one Whittaker factorisation in the Langlands–Tunnell input and for the corresponding statements about cuspidal constituents and isotypic weight-one forms at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.isArchSmoothAt_reflectedLowering_and_archCasimirAt_eq_and_reflectedLowering_reflectedLowering_eq_smul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (T : (AdelicGL2 (𝓞 F) F → ℂ) → AdelicGL2 (𝓞 F) F → ℂ)
    (hT : T = fun (θ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) =>
      (archDerivAt hw ArchDir.H θ - Complex.I • (archDerivAt hw ArchDir.E θ + archDerivAt hw ArchDir.Fm θ))
        (g * archRealGLAt hw UpperHalfPlane.J))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        archDerivAt hw ArchDir.E φ - archDerivAt hw ArchDir.Fm φ = Complex.I • φ) ∧
      IsArchSmoothAt hw (T φ) ∧
      (HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) (T φ)) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → archCasimirAt hw (T φ) = lam • T φ) ∧
      (∀ lam : ℂ, archCasimirAt hw φ = lam • φ → HasArchCharacterAt₀ F w (archWeightCharAt hw 1) φ →
        T (T φ) = (1 - 4 * lam) • φ) := by sorry
