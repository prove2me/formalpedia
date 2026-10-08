-- Prove2me | Theorems.Thm_ExtADMM_Diverge_theorem_3_1
-- name    : ExtADMM.Diverge.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:15.529452+00:00
-- url     : https://prove2.me/theorems/1b7448b9-6015-4ad6-9dc8-cb56bdba80d2
-- title:
--   Theorem 3.1, p. 14 — on the instance (3.10), the direct extension of ADMM diverges for every β > 0 from an open half of a 3-dimensional subspace of starting points
-- statement:
--   Consider the three-block problem (1.1) given by the linear system
--
--   $$A_1x_1+A_2x_2+A_3x_3=0,\qquad A=(A_1,A_2,A_3)=\begin{pmatrix}1&1&1\\1&1&2\\1&2&2\end{pmatrix},\quad x_i\in\mathbb R,$$
--
--   with null objective, $b=0$ and $\mathcal X_i=\mathbb R$ (example (3.10)). Then:
--
--   1. this instance satisfies the standing assumptions of (1.1) (closed convex sets, convex objectives, nonempty solution set);
--   2. there are a three-dimensional real subspace $S$ of $\mathbb R^5$ and a nonzero linear functional $\varphi$ on $S$ such that, for **every** penalty parameter $\beta>0$ and every starting point $(x_2^0,x_3^0,\lambda^0)\in\mathbb R\times\mathbb R\times\mathbb R^3$ with
--   $$z^0=\bigl(x_2^0,\ x_3^0,\ \lambda^0/\beta\bigr)\in S\quad\text{and}\quad\varphi(z^0)>0,$$
--   the direct extension of ADMM (1.5) with penalty $\beta$ has a run starting from $(x_2^0,x_3^0,\lambda^0)$, and **no** run from that starting point converges: the sequence $(x_1^k,x_2^k,x_3^k,\lambda^k)$ has no limit.
--
--   This is the paper's main theorem. It answers negatively the question whether the direct extension of the two-block ADMM to three blocks converges for convex problems: even on a nonsingular linear system with zero objective, for every $\beta>0$ and from an open half of a three-dimensional subspace of starting points, the iteration diverges.
--
--   **Formalization Note.** "There is an example" is witnessed by the paper's own instance (3.10). The paper's "continuously dense half space of dimension 3" is $\{z\in S:\varphi(z)>0\}$ in the coordinates $(x_2^0,x_3^0,\mu^0)$ with $\mu^0=\lambda^0/\beta$ of (3.12)–(3.13); in these coordinates the set does not depend on $\beta$, so $S$ and $\varphi$ are chosen before $\beta$. "Divergent" is read as "does not converge" (in the product topology of $\mathbb R\times\mathbb R\times\mathbb R\times\mathbb R^3$), and the existence of a run is asserted so that the claim is not vacuous. $x_1^0$ is not used by (1.5).
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 14, Theorem 3.1

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- Theorem 3.1, p. 14. The instance (3.10) of problem (1.1) satisfies the standing
assumptions, and there are a 3-dimensional subspace `S` of the space of starting points
`(x₂⁰, x₃⁰, λ⁰/β)` and a nonzero linear functional `φ` on `S` such that, for every penalty
`β > 0` and every starting point `(x₂⁰, x₃⁰, λ⁰)` with `(x₂⁰, x₃⁰, λ⁰/β)` in the open half
`{z ∈ S | φ z > 0}`, the direct extension of ADMM (1.5) has a run from that point, and no
run from that point converges. -/
theorem theorem_3_1 :
    example310.Standing ∧
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧ ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ β : ℝ, 0 < β → ∀ (x20 x30 : Fin 1 → ℝ) (lam0 : Fin 3 → ℝ)
        (hz : stateVec β x20 x30 lam0 ∈ S), 0 < φ ⟨_, hz⟩ →
          (∃ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
              example310.IsRun15 β x1 x2 x3 lam ∧ x2 0 = x20 ∧ x3 0 = x30 ∧ lam 0 = lam0) ∧
          ∀ (x1 x2 x3 : ℕ → Fin 1 → ℝ) (lam : ℕ → Fin 3 → ℝ),
            example310.IsRun15 β x1 x2 x3 lam → x2 0 = x20 → x3 0 = x30 → lam 0 = lam0 →
              ¬ ∃ w, Tendsto (fun k => (x1 k, x2 k, x3 k, lam k)) atTop (𝓝 w) := by sorry

end ExtADMM.Diverge
