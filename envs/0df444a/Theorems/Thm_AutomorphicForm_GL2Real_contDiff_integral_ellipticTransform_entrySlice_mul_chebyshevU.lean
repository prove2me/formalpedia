-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU
-- name    : AutomorphicForm.GL2Real.contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/cfa6af46-0bc7-5373-af63-01306de1b918
-- title:
--   Smoothness and support of the Chebyshev modes of the elliptic transform
-- statement:
--   Let $P$ be a real normed space, and let $\Phi\colon(\mathrm{Mat}_{2\times 2}(\mathbb R))\times P\to\mathbb C$ be $C^\infty$ with compact support, with $\mathrm{tsupport}\,\Phi$ contained in the set of pairs whose matrix component has invertible determinant; let $j\in\mathbb N$. For $p\in P$ the slice `entrySlice` $\Phi$ $p$ is the function on $\mathrm{GL}_2(\mathbb R)$ sending $g$ to $\Phi(g,p)$, and for $r,\theta\in\mathbb R$ the elliptic transform `ellipticTransform` of a function $f$ on $\mathrm{GL}_2(\mathbb R)$ is $0$ unless $r>0$, in which case it equals $4\sin^2\theta\int_{y>0}\int_{x\in\mathbb R} y^{-2}\bigl(f(n_{x,y}k_{r,\theta}n_{x,y}^{-1})+f(n_{x,y}k_{r,-\theta}n_{x,y}^{-1})\bigr)\,dx\,dy$, where $n_{x,y}=\begin{pmatrix}y&x\\0&1\end{pmatrix}$ for $y>0$ and $k_{r,\theta}=r\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}$. The assertion is a conjunction of three statements about the function $F(r,p)=\int_0^\pi \bigl(\mathrm{ellipticTransform}(\mathrm{entrySlice}\,\Phi\,p)\,r\,\theta\bigr)\cdot U_j(\cos\theta)\,d\theta$ on $\mathbb R\times P$, with $U_j$ the Chebyshev polynomial of the second kind of index $j$ (taken with integer index, coerced from $\mathbb R$ to $\mathbb C$): $F$ is $C^\infty$, $F$ has compact support, and $\mathrm{tsupport}\,F\subseteq (0,\infty)\times P$.
--
--   This is the regularity and support statement for the Chebyshev modes of the elliptic orbital data attached to a smooth compactly supported family of test functions on $\mathrm{GL}_2(\mathbb R)$; the change of variables underlying it is the elliptic coordinate computation [`AutomorphicForm.GL2Real.setIntegral_image_ellipticCoords_eq_integral_jacobian_smul`](thm.html#AutomorphicForm.GL2Real.setIntegral_image_ellipticCoords_eq_integral_jacobian_smul). It feeds the construction of smooth splitting data matching prescribed elliptic transforms, used in the analysis of discrete series pairings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.contDiff_integral_ellipticTransform_entrySlice_mul_chebyshevU
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      tsupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
          ellipticTransform (entrySlice Φ q.2) q.1 θ * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by sorry
