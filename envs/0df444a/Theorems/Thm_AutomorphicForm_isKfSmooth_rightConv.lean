-- Prove2me | Theorems.Thm_AutomorphicForm_isKfSmooth_rightConv
-- name    : AutomorphicForm.isKfSmooth_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0765bfd0-5640-5946-aac2-7f1b7cf1ab59
-- title:
--   Right convolution by a factorizable test function is K_f-smooth
-- statement:
--   Let $F$ be a number field, let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be an arbitrary function on the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$ (here $\mathbb{A}_F$ is the adele ring of $F$ built from $\mathcal{O}_F$), and let $f\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a factorizable test function, i.e. there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring such that: $f_\infty$ is of the form $g\mapsto \Phi(\text{matrix entries of } g)$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $F$, and has compact support; $f_{\mathrm{fin}}$ is locally constant with compact support; and $f(g)=f_\infty(\mathrm{glArch}(g))\cdot f_{\mathrm{fin}}(\mathrm{glFin}(g))$ for all $g$, where $\mathrm{glArch}$ and $\mathrm{glFin}$ are the maps induced on $\mathrm{GL}_2$ by the projections of $\mathbb{A}_F$ to its infinite and finite parts. Set $(\varphi * f)(g)=\int \varphi(gx)f(x)\,dx$, the integral taken against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_F)$ for the Borel $\sigma$-algebra. The conclusion is that $\varphi * f$ is $K_f$-smooth: inside the subgroup $\ker(\mathrm{glArch})$ of $\mathrm{GL}_2(\mathbb{A}_F)$, the stabiliser of $\varphi * f$ for the action by right translation is an open subset.
--
--   This is the standard smoothness statement for convolution operators on the adelic group: right convolution against a factorizable test function always lands in the space of functions invariant under an open subgroup of the finite-adelic points, with no hypothesis on $\varphi$. It is used throughout the construction of the cuspidal spectrum and the Hecke action, for instance in identifying lifts of coset sums and in the spherical-level arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isKfSmooth_rightConv.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm

theorem AutomorphicForm.isKfSmooth_rightConv
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) :
    IsKfSmooth F (rightConv F φ f) := by sorry
