-- Prove2me | Theorems.Thm_CauchyRiemannIndex_model_path_isCZValue
-- name    : CauchyRiemannIndex.model_path_isCZValue
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T11:15:28.826761+00:00
-- url     : https://prove2.me/theorems/b00d3666-614c-428b-b86c-7f7891702259
-- title:
--   Conley–Zehnder value of the model symplectic path
-- statement:
--   Let $k\in\mathbb{Z}$ and $\sigma>0$. The symplectic path
--   $$\psi(t)=R(\pi kt)\,H(\sigma t),\quad t\in[0,1],\qquad R(\theta)=\begin{pmatrix}\cos\theta&-\sin\theta\\ \sin\theta&\cos\theta\end{pmatrix},\quad H(s)=\begin{pmatrix}\cosh s&\sinh s\\ \sinh s&\cosh s\end{pmatrix},$$
--   has Conley–Zehnder value $k$. This is the path of the model asymptotic operators of Wendl, Lemma 5.29.
--
--   **Formalization Note** $\psi$ is any `C(unitInterval, Mat 1)` agreeing pointwise with the entrywise formula (`Matrix.fromBlocks` of $1\times1$ blocks); `IsCZValue` is the mission's definition (Gutt, Definition 7 with Corollary 12).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, Lemma 5.29, p. 103

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- For `k ∈ ℤ` and `σ > 0`, the path `ψ(t) = R(πkt) H(σt)`, `t ∈ [0, 1]`, with
`R(θ) = [[cos θ, -sin θ], [sin θ, cos θ]]` and `H(s) = [[cosh s, sinh s], [sinh s, cosh s]]`
written out entrywise, has Conley–Zehnder value `k`. -/
theorem model_path_isCZValue (k : ℤ) (σ : ℝ) (hσ : 0 < σ) (ψ : C(unitInterval, Mat 1))
    (hψ : ∀ t : unitInterval, ψ t = Matrix.fromBlocks
      (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.cosh (σ * t) -
        Real.sin (Real.pi * k * t) * Real.sinh (σ * t))
      (Matrix.of fun _ _ => Real.cos (Real.pi * k * t) * Real.sinh (σ * t) -
        Real.sin (Real.pi * k * t) * Real.cosh (σ * t))
      (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.cosh (σ * t) +
        Real.cos (Real.pi * k * t) * Real.sinh (σ * t))
      (Matrix.of fun _ _ => Real.sin (Real.pi * k * t) * Real.sinh (σ * t) +
        Real.cos (Real.pi * k * t) * Real.cosh (σ * t))) :
    IsCZValue ψ k := by
  sorry

end CauchyRiemannIndex
