-- Prove2me | Theorems.Thm_ConjGrad_Termination_cd_conjugacy_relations
-- name    : ConjGrad.Termination.cd_conjugacy_relations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:48:31.258872+00:00
-- url     : https://prove2.me/theorems/68c0a14c-21d5-4199-b224-220a53ea0701
-- title:
--   Theorem 4:1 — conjugacy and orthogonality relations of the cd-method, (4:3a)–(4:3c) and (4:4)
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k \in \mathbb{R}^n$, and let $x_i$, $r_i$, $p_i$ ($i = 0, 1, \dots$) be a run of the method of conjugate directions for $Ax = k$: $r_i = k - Ax_i$, $x_{i+1} = x_i + a_i p_i$ with $a_i = (p_i, r_i)/(p_i, Ap_i)$, and $(p_{i+1}, Ap_j) = 0$ for $j \le i$. Then
--
--   1. the directions are mutually conjugate: $(p_i, Ap_j) = 0$ for $i \ne j$ (4:3a);
--   2. the residual $r_i$ is orthogonal to $p_0, \dots, p_{i-1}$: $(p_j, r_i) = 0$ for $j < i$ (4:3b);
--   3. the inner product of $p_i$ with each of $r_0, \dots, r_i$ is the same (4:3c):
--   $$(p_i, r_0) = (p_i, r_1) = \cdots = (p_i, r_i);$$
--   4. the step length may be computed from the initial residual, (4:4): $x_{i+1} = x_i + a_i p_i$ with
--   $$a_i = \frac{(p_i, r_0)}{(p_i, Ap_i)}.$$
--
--   These relations are the basic properties of the cd-method. In particular (4:4) shows that the estimates can be computed without computing the intermediate residuals.
--
--   **Formalization Note** No direction is assumed nonzero: a zero direction gives a zero step ($0/0 = 0$ in Lean), and all four relations remain true for it. Item 4 is stated as the update of $x$, which is how (4:4) replaces (4:1a).
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 412, Theorem 4:1, eq. (4:3a)–(4:3c), (4:4); standing assumption (A symmetric positive definite) p. 410

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

/-- Theorem 4:1 (Hestenes–Stiefel 1952, p. 412). For every run of the cd-method with a
symmetric positive definite matrix `A`: (4:3a) the directions are mutually conjugate;
(4:3b) `rᵢ` is orthogonal to `p₀, …, pᵢ₋₁`; (4:3c) `(pᵢ, r₀) = (pᵢ, r₁) = ⋯ = (pᵢ, rᵢ)`;
(4:4) the step may be taken with `aᵢ = (pᵢ, r₀)/(pᵢ, Apᵢ)` in place of (4:1a). -/
theorem cd_conjugacy_relations {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) (x r p : ℕ → Fin n → ℝ) (hcd : IsCDRun A k x r p) :
    (∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0) ∧
    (∀ i j, j < i → p j ⬝ᵥ r i = 0) ∧
    (∀ i j, j ≤ i → p i ⬝ᵥ r j = p i ⬝ᵥ r 0) ∧
    (∀ i, x (i + 1) = x i + ((p i ⬝ᵥ r 0) / (p i ⬝ᵥ (A *ᵥ p i))) • p i) := by sorry

end ConjGrad.Termination
