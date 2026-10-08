-- Prove2me | Theorems.Thm_ExtADMM_Diverge_eq_3_12_3_13
-- name    : ExtADMM.Diverge.eq_3_12_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:58.434526+00:00
-- url     : https://prove2.me/theorems/6cbe22fd-12d1-4a3c-95ff-1dfb928dfa07
-- title:
--   (3.12)–(3.13), pp. 13–14 — a real 3-dimensional family of starting points along which Mᵏz is unbounded
-- statement:
--   Let $M$ be the $5\times5$ iteration matrix of example (3.10) (p. 12). There exist a three-dimensional real linear subspace $S\subseteq\mathbb R^5$ and a nonzero linear functional $\varphi:S\to\mathbb R$ such that for every $z\in S$ with $\varphi(z)\neq0$,
--
--   $$\|M^kz\|\to\infty\qquad(k\to\infty).$$
--
--   On the page, $S$ is the set of starting points $(x_2^0,x_3^0,\mu_1^0,\mu_2^0,\mu_3^0)=V(\alpha_1,\alpha_1,\alpha_2,\alpha_2,\alpha_3)^T$ of (3.13) with real $\alpha_i$, and $\varphi$ is the coordinate $\alpha_1$; in the eigen-coordinates $l=V^{-1}z$ of (3.12) the condition $\alpha_1\neq0$ means $l_1=l_2\neq0$, so the component along the eigenvalues of modulus $>1$ is present. Hence the iterates of (3.8) from such a starting point are unbounded, and cannot converge.
--
--   **Formalization Note.** The norm is the sup norm on $\mathbb R^5$; since all norms on $\mathbb R^5$ are equivalent, "$\|M^kz\|\to\infty$" does not depend on the choice. $S$ is existential because the paper's $V$ is printed only to four digits. Both requirements $\dim S=3$ and $\varphi\neq0$ are essential: without them the statement could be satisfied by $S=\{0\}$ or $\varphi=0$.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), pp. 13–14, (3.12)–(3.13) and the paragraph after (3.13)

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- (3.12)–(3.13), pp. 13–14. There are a 3-dimensional real subspace `S ⊆ ℝ⁵` (of starting
points `(x₂⁰, x₃⁰, μ₁⁰, μ₂⁰, μ₃⁰)`) and a nonzero linear functional `φ` on `S` (the
coordinate `α₁`) such that for every `z ∈ S` with `φ z ≠ 0` the iterates `Mᵏ z` of `M310` are
unbounded: `‖Mᵏ z‖ → ∞`. -/
theorem eq_3_12_3_13 :
    ∃ S : Submodule ℝ (Fin 5 → ℝ), Module.finrank ℝ S = 3 ∧ ∃ φ : S →ₗ[ℝ] ℝ, φ ≠ 0 ∧
      ∀ z : S, φ z ≠ 0 →
        Tendsto (fun k : ℕ => ‖(M310 ^ k) *ᵥ (z : Fin 5 → ℝ)‖) atTop atTop := by sorry

end ExtADMM.Diverge
