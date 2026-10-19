-- Prove2me | Theorems.Thm_CauchyRiemannIndex_joined_of_fundamentalSolution_close
-- name    : CauchyRiemannIndex.joined_of_fundamentalSolution_close
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:28:09.197576+00:00
-- url     : https://prove2.me/theorems/51d48eb2-d315-40d6-bd17-bc12240e9349
-- title:
--   Nondegenerate loops with uniformly close fundamental solutions are joined
-- statement:
--   Let $\psi:[0,1]\to\mathrm{Sp}(2n,\mathbb R)$ be continuous, with $1$ not an eigenvalue of $\psi(1)$. Then there is $\varepsilon>0$ with the following property. Let $S,S':\mathbb R\to\mathbb R^{2n\times2n}$ be continuous $1$-periodic loops of symmetric matrices with
--   $$S(0)=S'(0)=0,$$
--   whose asymptotic operators $-J_0\partial_t-S$ and $-J_0\partial_t-S'$ are nondegenerate, and let $\Psi,\Psi'$ be their fundamental solutions ($\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S\Psi$ on $\mathbb R$, and likewise for $S'$). If
--   $$\sup_{t\in[0,1]}\|\Psi(t)-\psi(t)\|<\varepsilon\quad\text{and}\quad\sup_{t\in[0,1]}\|\Psi'(t)-\psi(t)\|<\varepsilon$$
--   (entrywise maximum norm), then there is a continuous family $(S_\tau)_{\tau\in[0,1]}$ of continuous $1$-periodic loops of symmetric matrices from $S$ to $S'$ such that every $-J_0\partial_t-S_\tau$ is nondegenerate.
--
--   So, near any nondegenerate symplectic arc, nondegenerate asymptotic operators on the trivial bundle whose time-$[0,1]$ fundamental solutions follow the arc uniformly closely all lie in one path component of the space of nondegenerate asymptotic operators (Wendl, Lecture 3, §3.4). The radius $\varepsilon$ depends only on the arc $\psi$. The arc itself need not be differentiable.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The arc is `ψ : C(unitInterval, Mat n)` with `∀ t, IsSymplectic (ψ t)` and `(1 - ψ 1).det ≠ 0`. Loops satisfy `IsSymLoop` (continuous, $1$-periodic, symmetric values) and `IsNondegenerate`; `IsFundamentalSolution S Ψ` means $\Psi(0)=\mathrm{Id}$ and `HasDerivAt Ψ (J₀ n * S t * Ψ t) t` for all $t\in\mathbb R$. The uniform closeness on $[0,1]$ is written entrywise: `∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε`. The family is `H : C(unitInterval × ℝ, Mat n)` with `H (0, t) = S t`, `H (1, t) = S' t`, and `IsSymLoop`, `IsNondegenerate` for every slice `fun t => H (τ, t)`, the same form as Theorem 3.34.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- Around a path `ψ` in `SP(n)` there is a uniform neighbourhood such that any two nondegenerate
loops of symmetric matrices vanishing at `0`, whose fundamental solutions on `[0, 1]` lie in it,
are joined by a continuous family of nondegenerate loops of symmetric matrices. -/
theorem joined_of_fundamentalSolution_close (n : ℕ) (ψ : C(unitInterval, Mat n))
    (hψ : ∀ t, IsSymplectic (ψ t)) (hψ1 : (1 - ψ 1).det ≠ 0) :
    ∃ ε > 0, ∀ S S' Ψ Ψ' : ℝ → Mat n, IsSymLoop S → IsSymLoop S' → IsNondegenerate S →
      IsNondegenerate S' → S 0 = 0 → S' 0 = 0 → IsFundamentalSolution S Ψ →
      IsFundamentalSolution S' Ψ' → (∀ t : unitInterval, ∀ i j, |Ψ t i j - ψ t i j| < ε) →
      (∀ t : unitInterval, ∀ i j, |Ψ' t i j - ψ t i j| < ε) →
      ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧ (∀ t, H (1, t) = S' t) ∧
        ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  sorry

end CauchyRiemannIndex
