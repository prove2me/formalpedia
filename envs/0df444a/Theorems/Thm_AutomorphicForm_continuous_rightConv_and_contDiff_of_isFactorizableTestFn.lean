-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
-- name    : AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/ec6dc7d8-ea80-5bb1-87a5-7901301efdff
-- title:
--   Right convolution by a factorizable test function: continuity and Cᵈ⁺¹ regularity
-- statement:
--   Let $K$ be a number field, let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, where $\mathbb{A}_K$ denotes the adele ring of $K$ and $\mathrm{GL}_2$ is `AdelicGL2`, and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `IsFactorizableTestFn K f`, that is: there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles of $K$ and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles of $\mathcal{O}_K$ in $K$ such that $f_\infty$ has compact support and is of the form $g \mapsto \Phi(\mathrm{archEntries}\,g)$ for some $\Phi$ on the $2\times 2$ matrices over the mixed space of $K$ that is $C^\infty$ over $\mathbb{R}$, $f_{\mathrm{fin}}$ is locally constant with compact support, and $f(g) = f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$, the two factors being the archimedean and finite components of $g$. Write $(\varphi * f)(g) = \int \varphi(gx) f(x)\,d\mu(x)$ for `rightConv K φ f`, the integral against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ equipped with its Borel $\sigma$-algebra. The conclusion is twofold: $\varphi * f$ is continuous; and for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ the function $z \mapsto (\varphi * f)(n(z)\,g)$ on the mixed space of $K$, where $n(z)$ is the unipotent matrix $\begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ whose entry $t$ is the adele with archimedean part corresponding to $z$ under `InfiniteAdeleRing.ringEquiv_mixedSpace` and finite part $0$, is $C^{d+1}$ over $\mathbb{R}$, with $d = [K : \mathbb{Q}]$.
--
--   This is the standard regularity statement for right convolution of a continuous function on $\mathrm{GL}_2(\mathbb{A}_K)$ by a test function that is smooth and compactly supported at the archimedean places and locally constant with compact support at the finite places: continuity of the convolution, together with the finite order of differentiability needed along the archimedean unipotent directions. It is invoked throughout the later analysis of automorphic forms in this development, in particular in the estimates for class sums and in the study of constant terms and cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField
open scoped Classical in

theorem AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    Continuous (rightConv K φ f) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
          rightConv K φ f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g)) := by sorry
