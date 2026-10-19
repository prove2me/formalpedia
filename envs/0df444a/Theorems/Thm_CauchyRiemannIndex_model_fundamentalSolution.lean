-- Prove2me | Theorems.Thm_CauchyRiemannIndex_model_fundamentalSolution
-- name    : CauchyRiemannIndex.model_fundamentalSolution
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:15:26.774564+00:00
-- url     : https://prove2.me/theorems/b5a84afc-c18d-49ae-ab91-efa564b14066
-- title:
--   Fundamental solution of the model asymptotic operator
-- statement:
--   Let $k\in\mathbb{Z}$ and $\sigma\in\mathbb{R}$, and let $S(t)=\pi k\,\mathrm{Id}+\sigma\,A(e^{2\pi ikt})$ on $\mathbb{R}^2=\mathbb{C}$, where $A(\beta)$ is the real matrix of $z\mapsto\beta\bar z$. The fundamental solution of $\Psi'=J_0S\Psi$, $\Psi(0)=\mathrm{Id}$, is
--   $$\Psi(t)=R(\pi kt)\,H(\sigma t),\qquad R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\ \sin\theta&\cos\theta\end{pmatrix},\quad H(s)=\begin{pmatrix}\cosh s&\sinh s\\ \sinh s&\cosh s\end{pmatrix}.$$
--   This identifies the linearized flow of the model asymptotic operators of Wendl, Lemma 5.29.
--
--   **Formalization Note** $\Psi(t)$ is written out entrywise as a `Mat 1` (`Matrix.fromBlocks` of $1\times1$ blocks); $A(\beta)$ is `antilinearMat β`, and `IsFundamentalSolution` is the mission's predicate ($\Psi(0)=\mathrm{Id}$, $\Psi'(t)=J_0S(t)\Psi(t)$ for all $t\in\mathbb{R}$).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.29, p. 103

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- For `k ∈ ℤ` and `σ ∈ ℝ`, the fundamental solution of the loop
`S(t) = π k Id + σ · (z ↦ e^{2πikt} z̄)` is `Ψ(t) = R(πkt) H(σt)`, the product of the rotation
`R(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]` and the hyperbolic matrix
`H(s) = [[cosh s, sinh s], [sinh s, cosh s]]`, written out entrywise. -/
theorem model_fundamentalSolution (k : ℤ) (σ : ℝ) :
    IsFundamentalSolution (fun t : ℝ => (Real.pi * k) • (1 : Mat 1) +
        σ • antilinearMat (Complex.exp (2 * Real.pi * k * t * Complex.I)))
      (fun t : ℝ => Matrix.fromBlocks
        (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.cosh (σ * t) -
          Real.sin (Real.pi * k * t) * Real.sinh (σ * t))
        (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.sinh (σ * t) -
          Real.sin (Real.pi * k * t) * Real.cosh (σ * t))
        (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.cosh (σ * t) +
          Real.cos (Real.pi * k * t) * Real.sinh (σ * t))
        (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.sinh (σ * t) +
          Real.cos (Real.pi * k * t) * Real.cosh (σ * t))) := by
  sorry

end CauchyRiemannIndex
