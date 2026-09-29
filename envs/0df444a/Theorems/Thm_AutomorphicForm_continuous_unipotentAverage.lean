-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_unipotentAverage
-- name    : AutomorphicForm.continuous_unipotentAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/2b914c41-12c6-587d-9693-fe697548bedc
-- title:
--   Continuity of unipotent Schwartz–Bruhat averages on GL₂(A_F)
-- statement:
--   Let $F$ be a number field and write $\mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the group of invertible $2\times 2$ matrices over the adele ring of $F$. Let $G\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and of moderate growth in the sense that for some real $C$ and some natural number $M$ one has $\|G(g)\|\le C\,\bigl(\max(\|\det g\|,\|\det g\|^{-1})\bigr)^{M}$ for all $g$, where $\|\cdot\|$ is `ideleNorm F`, the value of the distributive Haar character of the adele ring at the given idele, viewed as a nonnegative real. Let $B\colon\mathbb{A}_F\to\mathbb{C}$ lie in [`NumberField.AdelicFourier.schwartzBruhat F`](def/NumberField_AdelicFourier.html#L80), the complex span of the functions $x\mapsto g(x_\infty)h(x_{\mathrm{fin}})$ with $g$ Schwartz on the mixed space of $F$ and $h$ locally constant with compact support on the finite adeles. Let $\Phi\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be any function satisfying, for every $h$, $$\Phi(h)=\int_{\mathbb{A}_F} B(x)\,G\bigl(h\cdot n(x)\bigr)\,dx,$$ the integral taken against the adelic additive Haar measure `adelicAddHaar` for the Borel $\sigma$-algebra on $\mathbb{A}_F$, with $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ the unipotent element `unipotentGL2 x`. Then $\Phi$ is continuous.
--
--   This is the continuity of a unipotent average of a moderate-growth function against a Schwartz–Bruhat weight, the basic regularity statement underlying the constant-term and Whittaker-type integrals on $\mathrm{GL}_2$ over the adeles. It is used by [`AutomorphicForm.continuous_unipotentAverage_rightConv`](thm.html#AutomorphicForm.continuous_unipotentAverage_rightConv), where the same average is taken in the presence of a right convolution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_unipotentAverage.lean

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm IsDedekindDomain NumberField.TateGlobal

theorem AutomorphicForm.continuous_unipotentAverage
    (F : Type) [Field F] [NumberField F]
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous G)
    (hMG : ∃ C : ℝ, ∃ M : ℕ, ∀ g : AdelicGL2 (𝓞 F) F,
      ‖G g‖ ≤ C * max (ideleNorm F (Matrix.GeneralLinearGroup.det g))
        (ideleNorm F (Matrix.GeneralLinearGroup.det g))⁻¹ ^ M)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    Continuous Φ := by sorry
