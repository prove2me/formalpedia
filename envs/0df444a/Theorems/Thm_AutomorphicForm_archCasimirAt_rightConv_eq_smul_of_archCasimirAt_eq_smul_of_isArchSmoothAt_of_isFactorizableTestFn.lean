-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
-- name    : AutomorphicForm.archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/004bf345-8c4c-5184-b92d-acb8e741360a
-- title:
--   Casimir eigenvalue persists under right convolution by a test function
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ assumed real, and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over the adele ring of $F$. Let $\varphi : G \to \mathbb{C}$ be continuous and smooth along the slices at $w$, in the sense of `IsArchSmoothAt`: for every $g \in G$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,e)$ on real $2 \times 2$ matrices $e$, where $\mathrm{archRealLiftAt}$ pushes an invertible real matrix into $G$ through the real place $w$ (and is $1$ when $\det e = 0$), is $C^\infty$ on $\{e : \det e \neq 0\}$. Let $\lambda \in \mathbb{C}$ and assume $\varphi$ is an eigenfunction of the Casimir operator at $w$, $\mathrm{archCasimirAt}\,\varphi = \lambda \cdot \varphi$, where $\mathrm{archCasimirAt}\,\varphi = -\bigl(\tfrac14 D_H D_H \varphi - \tfrac12 D_H \varphi + D_E D_{F^-}\varphi\bigr)$ and $D_d\psi(g)$ is the derivative at $t = 0$ of $t \mapsto \psi(g \cdot \mathrm{archFlowAt}\,d\,t)$ for the one-parameter flows in the directions $H$, $E$, $F^-$ at $w$. Let $f : G \to \mathbb{C}$ be a factorizable test function: $f(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ for the projections to $\mathrm{GL}_2$ of the infinite and finite adeles, with $f_\infty$ compactly supported and given by a $C^\infty$ function of the archimedean matrix entries in the mixed space of $F$, and $f_{\mathrm{fin}}$ locally constant with compact support. Then the right convolution $(\varphi * f)(g) = \int_G \varphi(gx) f(x)\,dx$, taken against the Haar measure on $G$ for its Borel $\sigma$-algebra, is again smooth along the slices at $w$ and satisfies $\mathrm{archCasimirAt}\,(\varphi * f) = \lambda \cdot (\varphi * f)$.
--
--   This is the standard fact that smoothing an automorphic function by a test function preserves the eigenvalue of the Casimir element at an archimedean place, in the concrete slice-smoothness formulation used here. It is invoked when passing from an arbitrary Casimir eigenfunction to convolved, slice-smooth representatives, notably in the construction of Casimir eigenvectors inside isotypic cuspidal and cut submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion AutomorphicForm

theorem AutomorphicForm.archCasimirAt_rightConv_eq_smul_of_archCasimirAt_eq_smul_of_isArchSmoothAt_of_isFactorizableTestFn
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hs : IsArchSmoothAt hw φ)
    (lam : ℂ) (hΩ : archCasimirAt hw φ = lam • φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsArchSmoothAt hw (rightConv F φ f) ∧ archCasimirAt hw (rightConv F φ f) = lam • rightConv F φ f := by sorry
