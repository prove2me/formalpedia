-- Prove2me | Theorems.Thm_AutomorphicForm_isKfSmooth_unipotentAverage
-- name    : AutomorphicForm.isKfSmooth_unipotentAverage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ed6c0c18-51d5-50ad-b94e-52e055d3700a
-- title:
--   K_f-smoothness of unipotent Schwartz–Bruhat averages
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the group of invertible $2\times 2$ matrices over the adele ring of $F$. Let $G\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy `IsKfSmooth F G`, i.e. the stabiliser of $G$, viewed as an element of the right-translation action of $\mathrm{GL}_2(\mathbb{A}_F)$ on functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$, intersected with the subgroup `finiteAdelicGL2Subgroup F` (the kernel of the archimedean-component homomorphism [`NumberField.AdelicLevel.glArch`](def/NumberField_AdelicLevel.html#L191)), is an open subset of that subgroup. Let $B\colon\mathbb{A}_F\to\mathbb{C}$ lie in the Schwartz–Bruhat space of $F$, the $\mathbb{C}$-span of the pure tensors $x\mapsto g(x_\infty)h(x_f)$ with $g$ a Schwartz function on the mixed space of $F$ and $h$ a locally constant, compactly supported function on the finite adeles. Let $\Phi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a function which at every $h$ is given by the integral, against the additive Haar measure `adelicAddHaar` on $\mathbb{A}_F$ with its Borel $\sigma$-algebra, of $x\mapsto B(x)\,G\bigl(h\cdot n(x)\bigr)$, where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then $\Phi$ is also $K_f$-smooth in the same sense.
--
--   This is the standard stability of the space of $K_f$-smooth (finite-adelically locally constant) functions on $\mathrm{GL}_2(\mathbb{A}_F)$ under averaging along the unipotent subgroup against a Schwartz–Bruhat weight, the operation used to form constant and Whittaker terms. It is invoked in the treatment of the Whittaker expansion of such unipotent averages along the diagonal torus and in the attendant integrability statement for the associated zeta integrands.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isKfSmooth_unipotentAverage.lean

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

theorem AutomorphicForm.isKfSmooth_unipotentAverage
    (F : Type) [Field F] [NumberField F]
    (G : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsKfSmooth F G)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    IsKfSmooth F Φ := by sorry
