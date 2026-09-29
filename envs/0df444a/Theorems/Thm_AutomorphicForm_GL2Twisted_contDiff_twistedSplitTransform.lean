-- Prove2me | Theorems.Thm_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform
-- name    : AutomorphicForm.GL2Twisted.contDiff_twistedSplitTransform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/8d31d41d-7b00-5629-8fc4-d79d13044b31
-- title:
--   Smoothness and symmetry of the twisted split transform
-- statement:
--   Let $P$ be a real normed space (a normed additive commutative group with a real normed space structure), and let $\Phi\colon (\mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{C}) \times P \to \mathbb{C}$ be a function of a pair consisting of the entry family of a complex $2\times 2$ matrix and a point of $P$. Assume $\Phi$ is $C^\infty$ over $\mathbb{R}$, has compact support, and that $\operatorname{tsupport}\Phi$ is contained in the set of pairs whose first coordinate, read as a matrix, has determinant a unit of $\mathbb{C}$, i.e. nonzero. For $p \in P$ write $\varphi_p(g) = \Phi(\text{entries of }g, p)$ for $g \in \mathrm{GL}_2(\mathbb{C})$, and let $H_p(a_1,a_2) = \mathtt{twistedSplitTransform}\,\varphi_p\,a_1\,a_2$, which for $a_1, a_2 > 0$ is $\int_{v \in \mathbb{C}} \mathtt{unitaryAverage}\bigl(k \mapsto \varphi_p(k^{-1}\, \left(\begin{smallmatrix}\sqrt{a_1} & v\\ 0 & \sqrt{a_2}\end{smallmatrix}\right)\, \bar{k})\bigr)$, with $\bar{k}$ the entrywise complex conjugate of $k$ and $\mathtt{unitaryAverage}$ the normalised iterated integral of $F$ against $\sin\eta\cos\eta$ over the parameters $(\psi,\eta,\xi_1,\xi_2)$ of $\mathtt{unitaryElt}$, and is $0$ otherwise. Then the map $(a_1,a_2,p) \mapsto H_p(a_1,a_2)$ on $\mathbb{R} \times \mathbb{R} \times P$ is $C^\infty$ over $\mathbb{R}$, has compact support, has $\operatorname{tsupport}$ contained in $\{a_1 a_2 \neq 0\}$, and satisfies $H_p(a_2,a_1) = H_p(a_1,a_2)$ for all $a_1, a_2 \in \mathbb{R}$ and $p \in P$.
--
--   This is the regularity input for the twisted (conjugation-twisted) split orbital data attached to a smooth compactly supported family of test functions on $\mathrm{GL}_2(\mathbb{C})$: smoothness in the split parameters and in the family parameter, compactness of support away from the coordinate axes, and the symmetry interchanging the two split eigenvalues. It is used in the construction of test functions with prescribed twisted orbital integrals, via [`AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq`](thm.html#AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_GL2Twisted_contDiff_twistedSplitTransform.lean

import Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.GL2Twisted

theorem AutomorphicForm.GL2Twisted.contDiff_twistedSplitTransform
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))}) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      HasCompactSupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ∧
      tsupport (fun q : ℝ × ℝ × P =>
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), q.2.2)) q.1 q.2.1) ⊆
        {q | q.1 * q.2.1 ≠ 0} ∧
      ∀ (a₁ a₂ : ℝ) (p : P),
        twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₂ a₁ =
          twistedSplitTransform (fun g => Φ (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℂ), p)) a₁ a₂ := by sorry
