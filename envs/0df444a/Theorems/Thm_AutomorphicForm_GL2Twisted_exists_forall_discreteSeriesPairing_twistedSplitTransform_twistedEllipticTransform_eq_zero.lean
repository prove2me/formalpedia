-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
-- name    : AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/0425a5e3-7941-5393-8f00-e0a26ddcf631
-- title:
--   Vanishing of large-weight discrete-series pairings of twisted transforms
-- statement:
--   Let $P$ be a real normed space and let $\Phi$ be a complex-valued function on pairs $(M,p)$, where $M$ is a $2\times 2$ matrix of complex entries (given as a function $\mathrm{Fin}\,2\to\mathrm{Fin}\,2\to\mathbb{C}$) and $p\in P$. Assume: $\Phi$ is $C^\infty$ for the real structure; $\Phi$ has compact support; the closed support of $\Phi$ is contained in the set of pairs with $\det M$ a unit; and both the $\mathbb{C}$-span of the right translates $(M,p)\mapsto\Phi(M\kappa,p)$ and the $\mathbb{C}$-span of the left translates $(M,p)\mapsto\Phi(\kappa M,p)$, as $\kappa$ runs over the subgroup `rowIsometrySubgroup₀ ℂ` of $\mathrm{GL}_2(\mathbb{C})$, are finite-dimensional over $\mathbb{C}$. Then there is an $N\in\mathbb{N}$, independent of $p$, such that for every $p\in P$, every natural number $k>N$ and every $r>0$ the weight-$k$ discrete-series pairing at radius $r$ of the pair $(H_p,E_p)$ vanishes, i.e.
--   $$\int_0^\pi E_p(r,\theta)\,U_{k-2}(\cos\theta)\,d\theta=\frac{2\pi}{r}\int_{\mathbb{R}}e^{-(k-1)|t|}\bigl(H_p(re^{t},re^{-t})+(-1)^kH_p(-re^{t},-re^{-t})\bigr)dt,$$
--   where $U$ denotes the Chebyshev polynomials of the second kind, and $H_p=$ `twistedSplitTransform`, $E_p=$ `twistedEllipticTransform` are formed from the slice $\varphi_p(g)=\Phi(\text{entries of }g,p)$ on $\mathrm{GL}_2(\mathbb{C})$: $H_p(a_1,a_2)$ is, for $a_1,a_2>0$, the integral over $v\in\mathbb{C}$ of the normalised unitary average of $\kappa\mapsto\varphi_p(\kappa^{-1}\,\left(\begin{smallmatrix}\sqrt{a_1}&v\\0&\sqrt{a_2}\end{smallmatrix}\right)\,\overline{\kappa})$ (and $0$ otherwise), and $E_p(r,\theta)$ is, for $r>0$, $4\sin^2\theta$ times the integral over $\rho>0$ and $u\in\mathbb{C}$ of $\rho^{-1}$ times the sum of the unitary averages of the conjugation-twisted translates of the elliptic elements at $(r,\theta)$ and $(r,-\theta)$ (and $0$ otherwise).
--
--   This is the large-weight vanishing statement for the archimedean twisted orbital data on $\mathrm{GL}_2(\mathbb{C})$, the twist being entrywise complex conjugation: for a bi-isometry-finite smooth test family supported over invertible matrices, all sufficiently high discrete-series pairings of its twisted split and elliptic transforms are zero, uniformly in the auxiliary parameter $p$. It is used by [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq) to produce test functions with prescribed twisted orbital integrals in the base-change comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real AutomorphicForm.GL2Twisted

theorem
AutomorphicForm.GL2Twisted.exists_forall_discreteSeriesPairing_twistedSplitTransform_twistedEllipticTransform_eq_zero
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2)))) :
    ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k
        (fun a₁ a₂ =>
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂)
        (fun r' θ =>
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r' θ)
        r = 0 := by sorry
