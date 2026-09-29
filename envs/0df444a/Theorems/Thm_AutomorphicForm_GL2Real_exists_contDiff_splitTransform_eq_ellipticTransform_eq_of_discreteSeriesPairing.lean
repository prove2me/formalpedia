-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
-- name    : AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/30b73a6c-7076-5e45-a644-dd13e5a664a8
-- title:
--   Bi-finite functions on GL₂(ℝ) with prescribed orbital transforms, in families
-- statement:
--   Let $P$ be a real normed space and let $H,E:\mathbb{R}\times\mathbb{R}\times P\to\mathbb{C}$. Assume: $H$ is $C^\infty$, compactly supported, with $\operatorname{tsupport}H\subseteq\{(a_1,a_2,p):a_1a_2\neq 0\}$, and symmetric, $H(a_2,a_1,p)=H(a_1,a_2,p)$; $E$ vanishes at $(r,\theta,p)$ whenever $(r,p)$ lies outside some compact $K\subseteq(0,\infty)\times P$, each $\theta\mapsto E(r,\theta,p)$ is interval integrable on $[0,\pi]$, $E$ is continuous on $\{0<r,\;0<\theta<\pi\}$, and for every $j\in\mathbb{N}$ the Chebyshev mode $(r,p)\mapsto\int_0^\pi E(r,\theta,p)U_j(\cos\theta)\,d\theta$ is $C^\infty$; finally there is $N$ such that for all $p$, all $k>N$ and all $r>0$ the pairing $\int_0^\pi E(r,\theta,p)U_{k-2}(\cos\theta)\,d\theta-\tfrac{2\pi}{r}\int_{\mathbb{R}}e^{-(k-1)|t|}\bigl(H(re^t,re^{-t},p)+(-1)^kH(-re^t,-re^{-t},p)\bigr)dt$ vanishes. Then there exists $F$ on (real $2\times2$ matrix entries) $\times\,P$, valued in $\mathbb{C}$, which is $C^\infty$, compactly supported, with $\operatorname{tsupport}F$ contained in the locus where the determinant is a unit, such that the $\mathbb{C}$-span of the right translates $M\mapsto F(Mk,p)$ and that of the left translates $M\mapsto F(kM,p)$, for $k$ ranging over `rowIsometrySubgroup₀ ℝ`, are both finite dimensional; such that every finite linear relation satisfied by the data is inherited: for $c:\mathrm{Fin}\,n\to\mathbb{C}$ and $q:\mathrm{Fin}\,n\to P$, if $\sum_j c_jH(a_1,a_2,q_j)=0$ for all $(a_1,a_2)$ and $\sum_j c_jE(r,\theta,q_j)=0$ for $r>0$, $0<\theta<\pi$, then $\sum_j c_jF(M,q_j)=0$ for every $M$; and such that, writing $f_p$ for the function $g\mapsto F(g,p)$ on $GL_2(\mathbb{R})$, one has $\frac{1}{2\pi}\int_0^{2\pi}\!\!\int_{\mathbb{R}}f_p\bigl(k_\theta\,\begin{pmatrix}a_1&u\\0&a_2\end{pmatrix}k_\theta^{-1}\bigr)du\,d\theta=H(a_1,a_2,p)$ whenever $a_1a_2\neq0$, and $4\sin^2\theta\int_{y>0}\!\int_{\mathbb{R}}\bigl(f_p(n_{x,y}\,rk_\theta\,n_{x,y}^{-1})+f_p(n_{x,y}\,rk_{-\theta}\,n_{x,y}^{-1})\bigr)y^{-2}dx\,dy=E(r,\theta,p)$ for $r>0$ and $0<\theta<\pi$, where $k_\theta$ is the rotation matrix and $n_{x,y}=\begin{pmatrix}y&x\\0&1\end{pmatrix}$.
--
--   This is the archimedean existence statement for test functions on $GL_2(\mathbb{R})$: prescribed split (hyperbolic) and elliptic orbital integrals, subject to the compatibility encoded by the vanishing of the discrete-series pairings in high weight, are realised by a smooth compactly supported function that is finite under left and right translation by the row-isometry subgroup, and the construction is linear in the data over a parameter space $P$. It feeds the comparison of twisted orbital integrals in [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq), the archimedean input to the trace-formula step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Polynomial AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (H : ℝ × ℝ × P → ℂ) (E : ℝ × ℝ × P → ℂ)
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H)
    (hHsupp : tsupport H ⊆ {q | q.1 * q.2.1 ≠ 0})
    (hHsym : ∀ (a₁ a₂ : ℝ) (p : P), H (a₂, a₁, p) = H (a₁, a₂, p))
    (hEc : ∃ K : Set (ℝ × P), IsCompact K ∧ K ⊆ Set.Ioi 0 ×ˢ Set.univ ∧
      ∀ (r θ : ℝ) (p : P), (r, p) ∉ K → E (r, θ, p) = 0)
    (hEi : ∀ (r : ℝ) (p : P), IntervalIntegrable (fun θ => E (r, θ, p)) volume 0 Real.pi)
    (hEcont : ContinuousOn E {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi})
    (hEmode : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) fun q : ℝ × P =>
      ∫ θ in (0 : ℝ)..Real.pi, E (q.1, θ, q.2) * (((Chebyshev.U ℝ (j : ℤ)).eval (Real.cos θ) : ℝ) : ℂ))
    (hvanish : ∃ N : ℕ, ∀ p : P, ∀ k > N, ∀ r > 0,
      discreteSeriesPairing k (fun a₁ a₂ => H (a₁, a₂, p)) (fun r' θ => E (r', θ, p)) r = 0) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ a : ℝ × ℝ, ∑ j, c j * H (a.1, a.2, q j) = 0) →
          (∀ b : ℝ × ℝ, 0 < b.1 → 0 < b.2 → b.2 < Real.pi → ∑ j, c j * E (b.1, b.2, q j) = 0) →
            ∀ M : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (M, q j) = 0) ∧
      (∀ (p : P) (a₁ a₂ : ℝ), a₁ * a₂ ≠ 0 → splitTransform (entrySlice F p) a₁ a₂ = H (a₁, a₂, p)) ∧
      (∀ (p : P) (r θ : ℝ), 0 < r → 0 < θ → θ < Real.pi →
        ellipticTransform (entrySlice F p) r θ = E (r, θ, p)) := by sorry
