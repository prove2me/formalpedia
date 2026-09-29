-- Prove2me | Theorems.Thm_AutomorphicForm_unipotentAverage_globalPoints_mul
-- name    : AutomorphicForm.unipotentAverage_globalPoints_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0db93221-8a01-5624-8d84-e0c13add7bbc
-- title:
--   Left GL₂(F)-invariance of unipotent averages
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$, and write $\mathrm{GL}_2(\mathbb{A}_F)$ for the group of invertible $2\times 2$ matrices over the adele ring of $F$. Let $G\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be any function that is invariant under left translation by global points, i.e. $G(\mathrm{globalPoints}(\gamma)\,g)=G(g)$ for all $\gamma\in\mathrm{GL}_2(F)$ and all $g\in\mathrm{GL}_2(\mathbb{A}_F)$, where `globalPoints` is the group homomorphism $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$ induced by the structure map $F\to\mathbb{A}_F$. Let $B\colon\mathbb{A}_F\to\mathbb{C}$ be an arbitrary function, and let $\Phi\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a function assumed to satisfy, for every $h$, $$\Phi(h)=\int_{\mathbb{A}_F} B(x)\,G\bigl(h\cdot u(x)\bigr)\,dx,$$ the Bochner integral against the additive Haar measure `adelicAddHaar` on $\mathbb{A}_F$ for its Borel measurable structure, where $u(x)$ denotes the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ with inverse $\begin{pmatrix}1&-x\\0&1\end{pmatrix}$. Then for every $\gamma\in\mathrm{GL}_2(F)$ and every $h\in\mathrm{GL}_2(\mathbb{A}_F)$ one has $\Phi(\mathrm{globalPoints}(\gamma)\,h)=\Phi(h)$. No integrability, measurability or decay hypothesis on $B$, $G$ or the product is imposed.
--
--   This is the elementary observation that the unipotent average $\Phi$ of a left $\mathrm{GL}_2(F)$-invariant function on $\mathrm{GL}_2(\mathbb{A}_F)$ against a weight $B$ on $\mathbb{A}_F$ is again left $\mathrm{GL}_2(F)$-invariant, left and right translations commuting. It is used in the adelic theory of automorphic forms on $\mathrm{GL}_2$ over $F$, where such averages feed the Whittaker coefficients and zeta integrals appearing in the statements [`AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage`](thm.html#AutomorphicForm.exists_forall_integrable_zetaIntegrand_whittakerCoefficient_unipotentAverage) and [`AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage`](thm.html#AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_unipotentAverage).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_unipotentAverage_globalPoints_mul.lean

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

theorem AutomorphicForm.unipotentAverage_globalPoints_mul
    (F : Type) [Field F] [NumberField F]
    (G : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      G (globalPoints (𝓞 F) F γ * g) = G g)
    (B : AdeleRing (𝓞 F) F → ℂ)
    (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ∀ h : AdelicGL2 (𝓞 F) F, Φ h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * G (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F)))
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (h : AdelicGL2 (𝓞 F) F) :
    Φ (globalPoints (𝓞 F) F γ * h) = Φ h := by sorry
