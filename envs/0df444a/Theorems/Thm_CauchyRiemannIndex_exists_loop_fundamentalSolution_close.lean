-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_loop_fundamentalSolution_close
-- name    : CauchyRiemannIndex.exists_loop_fundamentalSolution_close
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:28:08.720986+00:00
-- url     : https://prove2.me/theorems/adaa1479-67b4-450c-814e-448f577567d9
-- title:
--   Every nondegenerate symplectic arc is uniformly approximated by fundamental solutions
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2n,\mathbb R)$ be continuous with $\psi(0)=\mathrm{Id}$, such that $1$ is not an eigenvalue of $\psi(1)$, and let $\varepsilon>0$. Then there is a continuous $1$-periodic loop $S:\mathbb R\to\mathbb R^{2n\times2n}$ of symmetric matrices with $S(0)=0$, whose asymptotic operator $-J_0\partial_t-S$ is nondegenerate, such that its fundamental solution $\Psi$ ($\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S\Psi$ on $\mathbb R$) satisfies
--   $$\sup_{t\in[0,1]}\|\Psi(t)-\psi(t)\|<\varepsilon$$
--   in the entrywise maximum norm.
--
--   Thus the time-$[0,1]$ fundamental solutions of nondegenerate asymptotic operators on the trivial bundle are uniformly dense in the space $SP(n)$ of continuous nondegenerate symplectic arcs starting at the identity (Wendl, Lecture 3, §3.4), even under the normalization $S(0)=0$.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The arc is `ψ : C(unitInterval, Mat n)` with `∀ t, IsSymplectic (ψ t)`, `ψ 0 = 1` and `(1 - ψ 1).det ≠ 0`. Loops satisfy `IsSymLoop` (continuous, $1$-periodic, symmetric values) and `IsNondegenerate`; `IsFundamentalSolution S Ψ` means $\Psi(0)=\mathrm{Id}$ and `HasDerivAt Ψ (J₀ n * S t * Ψ t) t` for all $t\in\mathbb R$. The uniform closeness on $[0,1]$ is written entrywise: `∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Every path `ψ` in `SP(n)` is uniformly approximated on `[0, 1]` by the fundamental solution
of a nondegenerate loop of symmetric matrices vanishing at `0`. -/
theorem exists_loop_fundamentalSolution_close (n : ℕ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t, IsSymplectic (ψ t)) (hψ0 : ψ 0 = 1) (hψ1 : (1 - ψ 1).det ≠ 0) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ S Ψ : ℝ → Mat n, IsSymLoop S ∧ IsNondegenerate S ∧ S 0 = 0 ∧
      IsFundamentalSolution S Ψ ∧ ∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε := by
  sorry

end CauchyRiemannIndex
