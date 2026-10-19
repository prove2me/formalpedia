-- Prove2me | Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
-- name    : CauchyRiemannIndex.asymptoticCZIndex_eq_czIndex
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T12:12:53.919152+00:00
-- url     : https://prove2.me/theorems/6d0a17a2-b1a7-4590-af02-27e929673816
-- title:
--   The Conley–Zehnder index of an asymptotic operator is the index of its fundamental solution
-- statement:
--   Let $S:\mathbb R\to\mathbb R^{2n\times2n}$ be a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $-J_0\partial_t-S$ is nondegenerate, and let $\Psi$ be its fundamental solution ($\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S\Psi$). Let $\psi:[0,1]\to\mathbb R^{2n\times2n}$ be the restriction of $\Psi$ to $[0,1]$. Then
--   $$\mu_{CZ}(-J_0\partial_t-S)=\mu_{CZ}(\psi).$$
--
--   This identifies the chosen value `asymptoticCZIndex S` with the Conley–Zehnder index of the symplectic path $\psi$ (Gutt's definition), so that statements about one transfer to the other (Wendl, Definition 3.30, through the fundamental solution).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The loop is `IsSymLoop S`, nondegeneracy is `IsNondegenerate S`, the fundamental solution is any `Ψ` with `IsFundamentalSolution S Ψ`, and $\psi$ is any `ψ : C(unitInterval, Mat n)` with `ψ t = Ψ t`. The left side is `asymptoticCZIndex S` and the right side is `czIndex ψ`, both from the setting definitions.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- For a nondegenerate loop `S` of symmetric matrices with fundamental solution `Ψ`, the
Conley–Zehnder index of the asymptotic operator `-J₀ ∂ₜ - S` is the Conley–Zehnder index of the
path `Ψ|[0, 1]`. -/
theorem asymptoticCZIndex_eq_czIndex (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    asymptoticCZIndex S = czIndex ψ := by
  sorry

end CauchyRiemannIndex
