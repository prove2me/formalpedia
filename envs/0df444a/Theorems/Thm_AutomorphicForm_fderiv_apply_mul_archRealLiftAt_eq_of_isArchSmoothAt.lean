-- Prove2me | Theorems.Thm_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
-- name    : AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d68d2514-82b0-5207-8f15-6302e6ecf0b0
-- title:
--   Entry-chart derivative at a real place via H, E, F₋, centre
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $hw$ a witness that $w$ is real, and $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ a function on the units of the $2\times 2$ matrices over the adele ring of $\mathcal{O}_F \subset F$. Assume `IsArchSmoothAt hw φ`: for every $h$ the map $e' \mapsto \varphi(h \cdot \mathrm{archRealLiftAt}\,hw\,e')$ is $C^\infty$ on the set of $e' : \mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$ with $\det \ne 0$, where `archRealLiftAt` sends an invertible real matrix to its image in $\mathrm{GL}_2(\mathbb{A}_F)$ under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at $w$ (via the identification of $F_w$ with $\mathbb{R}$), and sends non-invertible matrices to $1$. Fix $g \in \mathrm{GL}_2(\mathbb{A}_F)$, a real matrix $e$ with $\det(e) \ne 0$, and an arbitrary real matrix $Y$. Writing $A = e^{-1}Y$, the assertion is that the real Fréchet derivative of $e' \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,hw\,e')$ at $e$, evaluated at $Y$, equals $$\tfrac{A_{00}-A_{11}}{2}\,\partial_H\varphi + A_{01}\,\partial_E\varphi + A_{10}\,\partial_{F_-}\varphi$$ all evaluated at $g\cdot\mathrm{archRealLiftAt}\,hw\,e$, plus $\tfrac{A_{00}+A_{11}}{2}$ times the derivative at $s = 0$ of $s \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,hw\,e \cdot \mathrm{archRealGLAt}\,hw(\exp(s)\cdot 1))$, the last argument being the scalar unit matrix with entry $\exp(s)$ placed at $w$; the real coefficients are coerced into $\mathbb{C}$. Here $\partial_d\varphi(h) = \mathrm{archDerivAt}\,hw\,d\,\varphi(h)$ is the derivative at $t=0$ of $t \mapsto \varphi(h\cdot\mathrm{archRealGLAt}\,hw(\mathrm{archFlowMatrix}\,d\,t))$, for the one-parameter families attached to the three directions `ArchDir.H`, `ArchDir.E`, `ArchDir.Fm`.
--
--   This is the first-order transport, at a real place, between derivatives taken in the matrix-entry chart of $\mathrm{GL}_2(\mathbb{R})$ and the right-invariant derivations along the split torus, the upper and lower unipotent one-parameter subgroups, together with the derivative along the archimedean centre. It is used in the construction of the archimedean differential operators, in particular by [`AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul`](thm.html#AutomorphicForm.hasDerivAt_apply_mul_archRealGLAt_inv_mul_archFlowMatrix_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace AutomorphicForm

theorem AutomorphicForm.fderiv_apply_mul_archRealLiftAt_eq_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ)
    (g : AdelicGL2 (𝓞 F) F) (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) (Y : Fin 2 → Fin 2 → ℝ) :
    fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℝ => φ (g * archRealLiftAt hw e')) e Y =
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 - ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          archDerivAt hw ArchDir.H φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 1 : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 1 0 : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ (g * archRealLiftAt hw e) +
      ((((Matrix.of e)⁻¹ * Matrix.of Y) 0 0 + ((Matrix.of e)⁻¹ * Matrix.of Y) 1 1) / 2 : ℝ) *
          deriv (fun s : ℝ => φ (g * archRealLiftAt hw e *
            archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom
              (Units.mk0 (Real.exp s) (Real.exp_ne_zero s))))) 0 := by sorry
