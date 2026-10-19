-- Prove2me | Theorems.Thm_CauchyRiemannIndex_symLoop_of_symplecticPath_family
-- name    : CauchyRiemannIndex.symLoop_of_symplecticPath_family
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T13:42:53.256863+00:00
-- url     : https://prove2.me/theorems/560bc6f6-2b40-4f4d-956c-1c062504b044
-- title:
--   Symplectic paths with vanishing end derivatives define nondegenerate loops
-- statement:
--   Let $\varphi:[0,1]\times\mathbb R\to\mathbb R^{2n\times2n}$ be continuous, $(s,t)\mapsto\varphi_s(t)$, such that each $\varphi_s$ is differentiable with derivative $\varphi_s'$, and $(s,t)\mapsto\varphi_s'(t)$ is continuous. Assume that for every $s\in[0,1]$
--   $$\varphi_s(t)\in\mathrm{Sp}(2n,\mathbb R)\ (t\in[0,1]),\qquad \varphi_s(0)=\mathrm{Id},\qquad \varphi_s'(0)=\varphi_s'(1)=0,$$
--   and that $1$ is not an eigenvalue of $\varphi_s(1)$. Put
--   $$S_s(t)=J_0\,\varphi_s'(\{t\})\,J_0\,\varphi_s(\{t\})^{T}J_0=-J_0\,\varphi_s'(\{t\})\,\varphi_s(\{t\})^{-1},$$
--   where $\{t\}=t-\lfloor t\rfloor$. Then $(s,t)\mapsto S_s(t)$ is continuous, every $S_s$ is a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $-J_0\partial_t-S_s$ is nondegenerate, and every fundamental solution $\Psi$ of $S_s$ ($\Psi(0)=\mathrm{Id}$, $\Psi'=J_0S_s\Psi$ on $\mathbb R$) coincides with $\varphi_s$ on $[0,1]$.
--
--   This is the passage from nondegenerate symplectic arcs to asymptotic operators on the trivial bundle (Wendl, Lecture 3, §3.4): a family of arcs that are $C^1$ and flat at the endpoints is realized, continuously in the parameter, as the family of time-$[0,1]$ fundamental solutions of nondegenerate asymptotic operators.
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`. The family is given by `φ φ' : unitInterval → ℝ → Mat n` with joint continuity of `fun p => φ p.1 p.2` and `fun p => φ' p.1 p.2`, `HasDerivAt (φ s) (φ' s t) t` for all $s,t$, `IsSymplectic (φ s t)` for $t\in[0,1]$, `φ s 0 = 1`, `φ' s 0 = 0`, `φ' s 1 = 0` and `(1 - φ s 1).det ≠ 0`. The loops are the slices of `H : C(unitInterval × ℝ, Mat n)` with `H (s, t) = J₀ n * φ' s (Int.fract t) * J₀ n * (φ s (Int.fract t))ᵀ * J₀ n`; the conclusion asserts `IsSymLoop`, `IsNondegenerate`, and `Ψ t = φ s t` on $[0,1]$ for every `Ψ` with `IsFundamentalSolution (fun t => H (s, t)) Ψ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, pp. 61-62 (Definition 3.30, Theorem 3.34), trivial bundle

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

/-- A continuous family of `C¹` paths in `Sp(2n)` on `[0, 1]`, starting at `Id` with vanishing
end derivatives and without eigenvalue `1` at time `1`, defines through
`t ↦ J₀ φ'(fract t) J₀ φ(fract t)ᵀ J₀ = -J₀ φ'(fract t) φ(fract t)⁻¹` a continuous family of
nondegenerate loops of symmetric matrices whose fundamental solutions are the given paths on
`[0, 1]`. -/
theorem symLoop_of_symplecticPath_family (n : ℕ) (φ φ' : unitInterval → ℝ → Mat n)
    (hφ : Continuous fun p : unitInterval × ℝ => φ p.1 p.2)
    (hφ' : Continuous fun p : unitInterval × ℝ => φ' p.1 p.2)
    (hd : ∀ s t, HasDerivAt (φ s) (φ' s t) t)
    (hs : ∀ s, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsSymplectic (φ s t))
    (h0 : ∀ s, φ s 0 = 1) (hd0 : ∀ s, φ' s 0 = 0) (hd1 : ∀ s, φ' s 1 = 0)
    (hn : ∀ s, (1 - φ s 1).det ≠ 0) :
    ∃ H : C(unitInterval × ℝ, Mat n),
      (∀ s t, H (s, t) = J₀ n * φ' s (Int.fract t) * J₀ n * (φ s (Int.fract t))ᵀ * J₀ n) ∧
      ∀ s, IsSymLoop (fun t => H (s, t)) ∧ IsNondegenerate (fun t => H (s, t)) ∧
        ∀ Ψ, IsFundamentalSolution (fun t => H (s, t)) Ψ → ∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ t = φ s t := by
  sorry

end CauchyRiemannIndex
