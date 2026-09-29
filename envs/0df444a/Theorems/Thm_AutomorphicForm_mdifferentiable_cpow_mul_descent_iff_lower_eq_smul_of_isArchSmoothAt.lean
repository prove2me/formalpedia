-- Prove2me | Theorems.Thm_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
-- name    : AutomorphicForm.mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c4c7c9d2-fa2b-5346-9c75-696081771344
-- title:
--   Holomorphy of y^σ-descents versus the lowering operator
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with `hw : w.IsReal`, and $\varphi$ a complex-valued function on `AdelicGL2 (𝓞 F) F`, the group of invertible $2\times 2$ matrices over the adele ring of $F$. Assume `IsArchSmoothAt hw φ`: for every $g$ the function $e \mapsto \varphi(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ on real $2\times 2$ matrices is $C^{\infty}$ on the open set where $\det e \neq 0$, where `archRealLiftAt` pushes an invertible real matrix into adelic $\mathrm{GL}_2$ through the place $w$. Let $m, c_0, \sigma \in \mathbb{C}$. Assume the infinitesimal weight relation $D_{E}\varphi - D_{\mathrm{Fm}}\varphi = m\varphi$, where $D_d\varphi(g)$ is `archDerivAt hw d φ`, the derivative at $t=0$ of $t \mapsto \varphi(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)$ along the one-parameter family of real matrices attached to the direction $d \in \{\mathrm{H},\mathrm{E},\mathrm{Fm}\}$ at $w$. Assume further the central exponent relation: for every $t \in \mathbb{R}^{\times}$ with $t > 0$ and every $g$, $\varphi(\iota_w(t\cdot 1)\,g) = t^{c_0}\varphi(g)$, where $\iota_w$ transports the scalar matrix $t\cdot 1$ along the inverse of the isomorphism $w$-completion $\cong \mathbb{R}$ and includes it into adelic $\mathrm{GL}_2$ at $w$. Then the following are equivalent: (i) for every $g$, the function $z \mapsto (\operatorname{Im} z)^{\sigma}\,\varphi\bigl(g\cdot\iota_w(\mathrm{iwasawaSectionGL}\,z)\bigr)$, with $\mathrm{iwasawaSectionGL}\,z = \begin{pmatrix} y & x \\ 0 & 1\end{pmatrix}$ for $z = x+iy$, is holomorphic on the upper half-plane (differentiable for the complex model with corners on source and target); (ii) $D_{\mathrm{H}}\varphi - i\,(D_{E}\varphi + D_{\mathrm{Fm}}\varphi) = (im - c_0 - 2\sigma)\,\varphi$.
--
--   This is the Maass–Cauchy–Riemann criterion in adelic form: holomorphy of the $y^{\sigma}$-renormalised descents of $\varphi$ to the upper half-plane along the Iwasawa section at the real place $w$ is equivalent to the weight-lowering operator acting on $\varphi$ by the scalar $im - c_0 - 2\sigma$. It is used in the comparison of lowest-weight vectors with holomorphy for functions carrying an archimedean character at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

theorem AutomorphicForm.mdifferentiable_cpow_mul_descent_iff_lower_eq_smul_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hs : IsArchSmoothAt hw φ) (m c₀ σ : ℂ)
    (hm : archDerivAt hw .E φ - archDerivAt hw .Fm φ = m • φ)
    (hc : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = (((t : ℝ) : ℂ) ^ c₀) * φ g) :
    (∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
          (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
            (iwasawaSectionGL z)))) ↔
      archDerivAt hw .H φ - Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) =
        (Complex.I * m - c₀ - 2 * σ) • φ := by sorry
