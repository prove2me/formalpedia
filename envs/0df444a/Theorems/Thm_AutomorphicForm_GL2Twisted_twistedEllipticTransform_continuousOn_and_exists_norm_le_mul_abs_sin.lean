-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
-- name    : AutomorphicForm.GL2Twisted.twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/c55be406-57d2-5426-91d4-d185cc0810aa
-- title:
--   Continuity, |sinθ| bound and support of twisted elliptic transforms
-- statement:
--   Let $P$ be a normed additive commutative group and let $\Phi$ be a complex-valued function of a pair consisting of a $2\times 2$ array of complex numbers and a point of $P$; assume $\Phi$ is continuous, has compact support, and that its topological support is contained in the set of pairs whose first component, read as a matrix, has invertible determinant. For $p \in P$ write $\varphi_p(g) = \Phi(\text{entries of } g, p)$ for $g \in \mathrm{GL}_2(\mathbb{C})$, and let $E_p(r,\theta) =$ `twistedEllipticTransform` $\varphi_p\, r\, \theta$, which for $r>0$ equals $4\sin^2\theta$ times $\int_{\rho>0}\int_{u\in\mathbb{C}} \rho^{-1}\bigl(A(\rho,u,\theta)+A(\rho,u,-\theta)\bigr)$, where $A(\rho,u,\theta)$ is the normalised average, over the four Euler-type angles $\psi,\xi_1,\xi_2\in[0,2\pi]$ and $\eta\in[0,\pi/2]$ with weight $\sin\eta\cos\eta$ and factor $1/(4\pi^3)$, of $\varphi_p(k^{-1}\,\gamma(r,\theta,\rho,u)\,\bar k)$ for $k$ the unitary element attached to those angles, $\bar k$ its entrywise complex conjugate and $\gamma(r,\theta,\rho,u)$ the explicit matrix of determinant $-r$; and $E_p(r,\theta)=0$ for $r\le 0$. The assertion is threefold: $(r,\theta,p)\mapsto E_p(r,\theta)$ is continuous on $\{r>0,\ 0<\theta<\pi\}$; for every compact $C \subseteq (0,\infty)$ there is $K$ with $\|E_p(r,\theta)\| \le K|\sin\theta|$ for all $r \in C$, $\theta \in (0,\pi)$ and all $p$; and there is a compact $K \subseteq (0,\infty)\times P$ such that $E_p(r,\theta)=0$ for all $\theta$ whenever $(r,p)\notin K$.
--
--   This collects the analytic properties — continuity in the interior, vanishing to order $|\sin\theta|$ at the endpoints $\theta \to 0,\pi$, and compactness of the support in the radius and parameter variables — of the twisted elliptic orbital data attached to a continuous compactly supported family of functions on $\mathrm{GL}_2(\mathbb{C})$, the twist being complex conjugation. It is used in the construction of smooth compactly supported test functions with prescribed twisted orbital integrals, via [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.twistedEllipticTransform_continuousOn_and_exists_norm_le_mul_abs_sin
    (P : Type) [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContinuousOn (fun q : ℝ × ℝ × P =>
        twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} ∧
      (∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi 0 →
        ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
          ‖twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ‖ ≤
            K * |Real.sin θ|) ∧
      ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
        ∀ (r θ : ℝ) (p : P), (r, p) ∉ K →
          twistedEllipticTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) r θ = 0 := by sorry
