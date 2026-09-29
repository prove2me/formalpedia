-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero
-- name    : AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/47aa37d3-bfa4-527f-9e6c-4113e38d4e3d
-- title:
--   Poisson-kernel term concentrates at the scalar r· 1
-- statement:
--   Let $P$ be a real normed space, and let $\Phi\colon (\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb R)\times P\to\mathbb C$ be smooth (of class $C^\infty$ over $\mathbb R$) with compact support. Fix $p\in P$ and a real $r>0$, and write $\Phi_p(M)=\Phi(M,p)$ for the partial function of the matrix variable, $e=\begin{pmatrix}0&0\\1&0\end{pmatrix}$ for the lower-left elementary matrix, and, for $\theta\in\mathbb R$ and $q=(u,v)$,
--   $$M_\pm(\theta,q)=\begin{pmatrix} r(\cos\theta\mp v) & \pm r\,(\sin^2\theta+v^2)/u\\ \mp r u & r(\cos\theta\pm v)\end{pmatrix}.$$
--   Then, as $\theta\to 0$ within $(0,\infty)$,
--   $$\sin\theta\int_{(0,\infty)\times\mathbb R}\frac{D\Phi_p(M_+(\theta,q))[e]-D\Phi_p(M_-(\theta,q))[e]}{\sin^2\theta+v^2}\,\mathrm d q\;\longrightarrow\;\frac{2\pi}{r}\,\Phi(r\cdot 1,p),$$
--   where $D$ denotes the Fréchet derivative of $\Phi_p$ in the matrix variable, the integral is taken with respect to Lebesgue measure on the region $u>0$, $v\in\mathbb R$, the real scalars $\sin\theta$, $(\sin^2\theta+v^2)^{-1}$ and $2\pi/r$ act by coercion to $\mathbb C$, and $r\cdot 1$ is $r$ times the identity matrix.
--
--   This is the Poisson-kernel (approximate identity) computation that isolates the singular contribution in the angular derivative of the elliptic orbital transform on $\mathrm{GL}_2(\mathbb R)$: the kernel $\sin\theta/(\sin^2\theta+v^2)$ concentrates at $v=0$ while the inner integral of the difference of unipotent directional derivatives is evaluated at the scalar matrix $r\cdot 1$. It feeds the evaluation of the jump constant in the limit formula, being used by [`AutomorphicForm.GL2Real.eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice`](thm.html#AutomorphicForm.GL2Real.eq_neg_eight_mul_pi_of_forall_tendsto_ellipticTransform_entrySlice) and by [`AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi`](thm.html#AutomorphicForm.GL2Real.exists_ne_zero_tendsto_ellipticTransform_entrySlice_div_sin_sub_div_nhdsWithin_Ioi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.tendsto_sin_mul_integral_fderiv_entrySlice_sub_div_nhdsWithin_Ioi_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ) (p : P) (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun θ : ℝ => (Real.sin θ : ℂ) * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.univ,
        (((Real.sin θ ^ 2 + q.2 ^ 2)⁻¹ : ℝ) : ℂ) *
          (fderiv ℝ (fun M => Φ (M, p))
              (Matrix.of.symm !![r * (Real.cos θ - q.2), r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1);
                -(r * q.1), r * (Real.cos θ + q.2)])
              (Matrix.of.symm !![0, 0; 1, 0]) -
            fderiv ℝ (fun M => Φ (M, p))
              (Matrix.of.symm !![r * (Real.cos θ + q.2), -(r * ((Real.sin θ ^ 2 + q.2 ^ 2) / q.1));
                r * q.1, r * (Real.cos θ - q.2)])
              (Matrix.of.symm !![0, 0; 1, 0])))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (((2 * Real.pi / r : ℝ) : ℂ) * Φ (Matrix.of.symm (r • 1), p))) := by sorry
