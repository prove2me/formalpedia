-- Prove2me | Theorems.Thm_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
-- name    : AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/cd94f51e-2ee0-52a6-a71e-ee09ec2c5ec1
-- title:
--   Differentiating right convolution along archimedean unipotent directions
-- statement:
--   Let $K$ be a number field, let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, and let $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be a factorizable test function, i.e. $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm f}(\mathrm{glFin}\,g)$ for some $f_\infty$ on $\mathrm{GL}_2(K_\infty)$ of the form $\Phi\circ\mathrm{archEntries}$ with $\Phi$ a $C^\infty$ function of the entry array valued in the mixed space of $K$, $f_\infty$ of compact support, and some locally constant compactly supported $f_{\mathrm f}$ on $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm f})$. Write $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, let $e$ denote the canonical ring isomorphism from $K_\infty$ to the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$, and for $v$ in the mixed space and $t\in\mathbb{R}$ let $n(tv)$ be the adelic unipotent matrix with archimedean entry $e^{-1}(t\cdot v)$ and finite entry $0$; right convolution is $(\varphi*f)(g)=\int \varphi(gx)f(x)\,dx$ against the Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure. Put $L_vf(y)=\frac{d}{dt}\big|_{t=0}f(n(-tv)\,y)$. Then: (i) for every $v$ and every $g$, the function $t\mapsto(\varphi*f)(g\,n(tv))$ has derivative $(\varphi*L_vf)(g)$ at $t=0$; (ii) for every $v$, $L_vf$ is again a factorizable test function in the above sense; (iii) for all $a,b\in\mathbb{R}$, all $v,w$ in the mixed space and all $y$, $L_{a v+b w}f(y)=a\,L_vf(y)+b\,L_wf(y)$.
--
--   This is the standard smoothing mechanism on an adelic group: convolution on the right by a test function allows differentiation along a one-parameter archimedean unipotent subgroup, the derivative being again a convolution by a test function, depending linearly on the direction. It is used in the proofs of the bounds for Whittaker coefficients of right convolutions at diagonal elements, namely [`AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_mul_norm_infinitePlace_rpow_neg) and [`AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le`](thm.html#AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear.lean

import Mathlib
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm
open scoped Classical in

theorem AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f) :
    (∀ (v : mixedEmbedding.mixedSpace K) (g : AdelicGL2 (𝓞 K) K),
        HasDerivAt (fun t : ℝ => rightConv K φ f (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
          (rightConv K φ (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) g) 0) ∧
    (∀ v : mixedEmbedding.mixedSpace K,
        IsFactorizableTestFn K (fun y => deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) ∧
    (∀ (a b : ℝ) (v w : mixedEmbedding.mixedSpace K) (y : AdelicGL2 (𝓞 K) K),
        deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • (a • v + b • w))), 0) * y)) 0 =
          a * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0 +
            b * deriv (fun t : ℝ => f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • w)), 0) * y)) 0) := by sorry
