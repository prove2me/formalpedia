-- Prove2me | Theorems.Thm_BregmanPPA_Convergence_step1
-- name    : BregmanPPA.Convergence.step1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:21:25.292086+00:00
-- url     : https://prove2.me/theorems/b7a37edf-404c-42ad-8862-4590740aa0d2
-- title:
--   Theorem 1, Step 1 — decreasing Bregman distances and bounded iterates
-- statement:
--   Consider a Bregman proximal-point run $(x^k)$ for a maximal monotone operator $T$ with $\operatorname{dom}T\subseteq\overline S$, positive step sizes bounded below by a positive constant, and a Bregman function $h$ with zone $S$. For every zero $z$ of $T$ and every $k\ge0$,
--
--   $$D_h(z,x^{k+1})\le D_h(z,x^k)-D_h(x^{k+1},x^k).$$
--
--   Moreover, $D_h(z,x^k)$ tends to a nonnegative real limit and the sequence $(x^k)$ is bounded.
--
--   This gives the distance and compactness estimates used in the convergence argument.
--
--   **Formalization Note** The paper's Step 1 writes $T^{-1}(0)\subseteq S$; under (C2), the stated standing assumption yields only $T^{-1}(0)\subseteq\overline S$. The inequality and boundedness use this latter inclusion, since Definition 1 defines $D_h$ on $\overline S\times S$.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 207, Theorem 1 proof, Step 1, https://doi.org/10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence Filter Topology

namespace BregmanPPA.Convergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 1, proof, Step 1: decreasing Bregman distance and bounded iterates. -/
theorem step1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    (∀ k, bregmanD h z (x (k + 1)) ≤
      bregmanD h z (x k) - bregmanD h (x (k + 1)) (x k)) ∧
    (∃ δ : ℝ, 0 ≤ δ ∧ Tendsto (fun k => bregmanD h z (x k)) atTop (𝓝 δ)) ∧
    Bornology.IsBounded (Set.range x) := by sorry

end BregmanPPA.Convergence
