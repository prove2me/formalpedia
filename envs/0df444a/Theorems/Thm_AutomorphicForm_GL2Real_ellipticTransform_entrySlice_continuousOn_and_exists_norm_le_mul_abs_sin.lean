-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin
-- name    : AutomorphicForm.GL2Real.ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ad5f6517-d0a5-5e31-8f5c-4c76c08c1787
-- title:
--   Continuity and |sinθ| bound for elliptic transforms
-- statement:
--   Let $P$ be a normed additive commutative group and let $\Phi : (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}) \times P \to \mathbb{C}$ be continuous, with compact support, and such that $\mathrm{tsupport}\,\Phi$ is contained in the set of pairs $q$ whose matrix component has determinant a unit of $\mathbb{R}$ (i.e. nonzero). For $p \in P$ write $\Phi_p$ for the slice `entrySlice Φ p`, the function on $GL_2(\mathbb{R})$ sending $g$ to $\Phi$ of the entry matrix of $g$ paired with $p$, and for $r>0$ let $$\mathcal{E}(\Phi_p)(r,\theta) = 4\sin^2\theta \int_{y>0}\int_{x\in\mathbb{R}} \frac{\Phi_p\bigl(n_{x,y}\,k_{r,\theta}\,n_{x,y}^{-1}\bigr)+\Phi_p\bigl(n_{x,y}\,k_{r,-\theta}\,n_{x,y}^{-1}\bigr)}{y^2}\,dx\,dy,$$ where $n_{x,y}=\begin{pmatrix} y & x\\ 0 & 1\end{pmatrix}$ and $k_{r,\theta}=\begin{pmatrix} r\cos\theta & r\sin\theta\\ -r\sin\theta & r\cos\theta\end{pmatrix}$, the value being $0$ when $r \le 0$. Two assertions are made. First, $(r,\theta,p)\mapsto \mathcal{E}(\Phi_p)(r,\theta)$ is continuous on the subset of $\mathbb{R}\times\mathbb{R}\times P$ cut out by $0<r$, $0<\theta<\pi$ (no restriction on $p$). Second, for every compact $C \subseteq (0,\infty)$ there is a real $K$ with $\|\mathcal{E}(\Phi_p)(r,\theta)\| \le K\,|\sin\theta|$ for all $r \in C$, all $\theta \in (0,\pi)$ and all $p \in P$.
--
--   This records the analytic properties of the elliptic orbital transform of a continuous compactly supported family of functions on $GL_2(\mathbb{R})$: joint continuity in the radius, the angle and the parameter on the open region $0<\theta<\pi$, together with vanishing of order at least one in $|\sin\theta|$ as $\theta \to 0$ or $\theta \to \pi$, uniformly in the parameter and locally uniformly in $r$. It is used in the construction of a smooth test function with prescribed split and elliptic transforms attached to a discrete series pairing, via [`AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing`](thm.html#AutomorphicForm.GL2Real.exists_contDiff_splitTransform_eq_ellipticTransform_eq_of_discreteSeriesPairing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.ellipticTransform_entrySlice_continuousOn_and_exists_norm_le_mul_abs_sin
    (P : Type) [NormedAddCommGroup P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦinv : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContinuousOn (fun q : ℝ × ℝ × P => ellipticTransform (entrySlice Φ q.2.2) q.1 q.2.1)
        {q | 0 < q.1 ∧ 0 < q.2.1 ∧ q.2.1 < Real.pi} ∧
      ∀ C : Set ℝ, IsCompact C → C ⊆ Set.Ioi 0 →
        ∃ K : ℝ, ∀ r ∈ C, ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi, ∀ p : P,
          ‖ellipticTransform (entrySlice Φ p) r θ‖ ≤ K * |Real.sin θ| := by sorry
