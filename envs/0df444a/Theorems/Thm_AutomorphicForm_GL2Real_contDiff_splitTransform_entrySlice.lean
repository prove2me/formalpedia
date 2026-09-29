-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice
-- name    : AutomorphicForm.GL2Real.contDiff_splitTransform_entrySlice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/14da0066-3e42-50f2-9e69-2ddc0d465745
-- title:
--   Smoothness and symmetry of split transforms in families
-- statement:
--   Let $P$ be a real normed space (a normed additive commutative group with a real normed space structure), and let $\Phi \colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}) \times P \to \mathbb{C}$ be a function of a pair consisting of a real $2 \times 2$ entry array and a point of $P$. Assume $\Phi$ is $C^\infty$ over $\mathbb{R}$, has compact support, and satisfies $\operatorname{tsupport} \Phi \subseteq \{q : \operatorname{det}(q_1) \text{ is a unit in } \mathbb{R}\}$, i.e. the closed support of $\Phi$ meets only pairs whose matrix is invertible. For $p \in P$ write $\Phi_p$ for the function on $\mathrm{GL}_2(\mathbb{R})$ sending $g$ to $\Phi$ of the entry array of $g$ together with $p$, and for $a_1, a_2 \in \mathbb{R}$ let $H_p(a_1,a_2)$ be the split transform of $\Phi_p$: if $a_1 a_2 \neq 0$, it is $\frac{1}{2\pi}\int_0^{2\pi}\!\int_{\mathbb{R}} \Phi_p\big(R(\theta)\,U(a_1,a_2,u)\,R(\theta)^{-1}\big)\,du\,d\theta$, where $R(\theta) = \begin{pmatrix} \cos\theta & \sin\theta \\ -\sin\theta & \cos\theta\end{pmatrix}$ and $U(a_1,a_2,u) = \begin{pmatrix} a_1 & u \\ 0 & a_2\end{pmatrix}$, and it is $0$ if $a_1 a_2 = 0$. The conclusion is a conjunction of four assertions about the function $(a_1,a_2,p) \mapsto H_p(a_1,a_2)$ on $\mathbb{R} \times \mathbb{R} \times P$: it is $C^\infty$ over $\mathbb{R}$; it has compact support; its closed support is contained in $\{(a_1,a_2,p) : a_1 a_2 \neq 0\}$; and $H_p(a_2,a_1) = H_p(a_1,a_2)$ for all $a_1, a_2 \in \mathbb{R}$ and all $p \in P$.
--
--   This is the regularity statement for the split (hyperbolic) orbital data attached to a smooth compactly supported family of functions on $\mathrm{GL}_2(\mathbb{R})$, recording smoothness in the split parameters and the auxiliary parameter, compact support away from the coordinate axes, and invariance under interchanging the two split eigenvalues. It is used in the construction of test functions with prescribed split and elliptic orbital transforms matching a discrete series pairing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Real_contDiff_splitTransform_entrySlice.lean

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Real

theorem AutomorphicForm.GL2Real.contDiff_splitTransform_entrySlice
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℝ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P => splitTransform (entrySlice Φ q.2.2) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        splitTransform (entrySlice Φ p) a₂ a₁ = splitTransform (entrySlice Φ p) a₁ a₂ := by sorry
