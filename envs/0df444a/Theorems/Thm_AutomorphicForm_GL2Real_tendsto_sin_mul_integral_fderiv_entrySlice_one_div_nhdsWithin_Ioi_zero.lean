-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
-- name    : AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3f4d292b-6f16-5feb-a60d-02f2de4513b1
-- title:
--   Vanishing of the first term in the elliptic jump relation
-- statement:
--   Let $P$ be a real normed space and let $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}) \times P \to \mathbb{C}$ be a smooth ($C^\infty$ over $\mathbb{R}$) function with compact support; fix $p \in P$ and a real $r > 0$. Write $u = q_1$, $v = q_2$ and let $M_\pm(\theta,u,v)$ be the real $2\times 2$ matrices $$M_+ = \begin{pmatrix} r(\cos\theta - v) & r\,\frac{\sin^2\theta + v^2}{u} \\ -ru & r(\cos\theta + v)\end{pmatrix},\qquad M_- = \begin{pmatrix} r(\cos\theta + v) & -r\,\frac{\sin^2\theta + v^2}{u} \\ ru & r(\cos\theta - v)\end{pmatrix},$$ viewed as elements of $\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$. The assertion is that $$\sin\theta \int_{(0,\infty)\times\mathbb{R}} \frac{D\big(\Phi(\cdot,p)\big)\big(M_+\big)[I] + D\big(\Phi(\cdot,p)\big)\big(M_-\big)[I]}{u}\, \mathrm{d}u\,\mathrm{d}v \longrightarrow 0$$ as $\theta \to 0$ within $(0,\infty)$, where $D\big(\Phi(\cdot,p)\big)(M)[I]$ denotes the Fréchet derivative of $M \mapsto \Phi(M,p)$ at $M$ evaluated at the identity matrix $\begin{pmatrix}1&0\\0&1\end{pmatrix}$, the integral is the Bochner integral of the $\mathbb{C}$-valued integrand against Lebesgue measure on the product region, and the quotient by $u$ is taken in $\mathbb{C}$.
--
--   The matrices $M_\pm(\theta,u,v)$ have determinant $r^2$ and trace $2r\cos\theta$, so they parametrise the elliptic conjugacy classes approaching the scalar $r\cdot I$; the displayed quantity is one of the two terms into which the angular derivative of the normalised elliptic orbital transform splits after integration by parts, and the statement is that this term contributes nothing to the jump at the scalar. It feeds into [`AutomorphicForm.GL2Real.eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice`](thm.html#AutomorphicForm.GL2Real.eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice) and [`AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi`](thm.html#AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi), which establish the $\mathrm{GL}_2(\mathbb{R})$ form of Harish-Chandra's limit formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_one_div_nhdsWithin_Ioi_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
              -(r * q.1), r * (Real.cos θ + q.2)])
            (Matrix.of.symm !![1, 0; 0, 1]) +
          fderiv ℝ (fun M => Φ (M, p))
            (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
              r * q.1, r * (Real.cos θ - q.2)])
            (Matrix.of.symm !![1, 0; 0, 1])) / (q.1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry
