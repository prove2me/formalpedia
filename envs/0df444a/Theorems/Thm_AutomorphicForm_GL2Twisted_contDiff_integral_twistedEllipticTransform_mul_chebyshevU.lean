-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU
-- name    : AutomorphicForm.GL2Twisted.contDiff_integral_twistedEllipticTransform_mul_chebyshevU
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ffc8ffdb-6755-5364-a587-339ec996e992
-- title:
--   Smoothness of the Chebyshev modes of the twisted elliptic transform
-- statement:
--   Let $P$ be a real normed space, let $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{C}) \times P \to \mathbb{C}$ be a function of a complex $2 \times 2$ array of entries and a parameter in $P$ which is $C^\infty$ over $\mathbb{R}$, has compact support, and whose closed support is contained in the set of pairs whose first component has determinant a unit of $\mathbb{C}$, and let $j$ be a natural number. Write $\varphi_p(g) = \Phi(g, p)$ for $g \in \mathrm{GL}_2(\mathbb{C})$, read through the entries of $g$. The assertion is that the function $(r,p) \mapsto \int_0^{\pi} \mathrm{twistedEllipticTransform}(\varphi_p)(r,\theta)\, U_j(\cos\theta)\, d\theta$ on $\mathbb{R} \times P$, where $U_j$ is the Chebyshev polynomial of the second kind of index $(j : \mathbb{Z})$ over $\mathbb{R}$ evaluated at $\cos\theta$, is $C^\infty$ over $\mathbb{R}$, is compactly supported, and has closed support contained in $\mathrm{Ioi}(0) \times P$. Here $\mathrm{twistedEllipticTransform}(\varphi)(r,\theta)$ vanishes unless $r > 0$, in which case it is $4\sin^2\theta$ times the integral over $\rho \in (0,\infty)$ and $u \in \mathbb{C}$ of $\rho^{-1}$ times the sum, for the angles $\theta$ and $-\theta$, of the unitary averages of $k \mapsto \varphi(k^{-1}\cdot \mathrm{twistedEllipticElt}(r,\pm\theta,\rho,u)\cdot \bar{k})$, with $\bar{k}$ the entrywise complex conjugate of $k$, the unitary average being the normalised integral $(4\pi^3)^{-1}\int\!\!\int\!\!\int\!\!\int \sin\eta\cos\eta\, F(\mathrm{unitaryElt}\,\psi\,\eta\,\xi_1\,\xi_2)$ over $\psi,\xi_1,\xi_2 \in [0,2\pi]$, $\eta \in [0,\pi/2]$, and $\mathrm{twistedEllipticElt}(r,\theta,\rho,u)$ the explicit matrix of determinant $-r$ recorded in the definition.
--
--   This is the regularity statement for the individual Chebyshev modes of the twisted (conjugation-twisted) elliptic orbital data attached to a smooth compactly supported family of functions on $\mathrm{GL}_2(\mathbb{C})$, the modes being the coefficients in the expansion of the transform in $\theta$ along the polynomials $U_j(\cos\theta)$. It feeds the construction of smooth compactly supported test functions with prescribed twisted orbital integrals, [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_contDiff_integral_twistedEllipticTransform_mul_chebyshevU.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.RingTheory.Polynomial.Chebyshev

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.contDiff_integral_twistedEllipticTransform_mul_chebyshevU
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      HasCompactSupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ∧
      tsupport (fun q : ℝ × P => ∫ θ in (0 : ℝ)..Real.pi,
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2)) q.1 θ *
            (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ)) ⊆
        Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set P) := by sorry
