-- Prove2me | Theorems.Thm_CompOT_Duality_eq_3_5
-- name    : CompOT.Duality.eq_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:51.814015+00:00
-- url     : https://prove2.me/theorems/7e473752-ca2f-405f-b170-7e888cc9b2eb
-- title:
--   (3.5), p. 403 — semi-dual: L_C(a, b) = max over f ∈ ℝⁿ of ⟨f, a⟩ + ⟨f^C, b⟩
-- statement:
--   Let $a \in \Sigma_n$, $b \in \Sigma_m$ be histograms and $C \in \mathbb R^{n\times m}$. Then
--   $$L_C(a,b) = \max_{f\in\mathbb R^n} \langle f,a\rangle + \langle f^C,b\rangle,$$
--   where $(f^C)_j = \min_i C_{i,j} - f_i$. Precisely: there exist a coupling $P\in\mathbf U(a,b)$ attaining $L_C(a,b) = \langle C,P\rangle$ and a vector $f\in\mathbb R^n$ such that $\langle f',a\rangle + \langle f'^C,b\rangle \le \langle f,a\rangle + \langle f^C,b\rangle$ for every $f'\in\mathbb R^n$, and $\langle C,P\rangle = \langle f,a\rangle + \langle f^C,b\rangle$.
--
--   This reformulates the dual problem as the maximization of a piecewise affine concave function of the single variable $f$; it is the starting point of the semi-discrete methods of §5.1.
--
--   **Formalization Note** The maximum ranges over all of $\mathbb R^n$ with no constraint, as in the book. $a\in\Sigma_n$ forces $n\ge1$, so $f^C$ is a genuine minimum.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §3.2, (3.5), p. 403

import Mathlib
import Definitions.Def_CompOT_Duality_Defs

namespace CompOT.Duality

/-- The semi-dual (3.5), p. 403: for histograms `a ∈ Σ_n`, `b ∈ Σ_m`,
`L_C(a, b) = max_{f ∈ ℝⁿ} ⟨f, a⟩ + ⟨f^C, b⟩`: some `P ∈ U(a, b)` attains `L_C(a, b)`, some `f`
attains the maximum over all of `ℝⁿ`, and the two values coincide. -/
theorem eq_3_5 {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (C : Matrix (Fin n) (Fin m) ℝ) :
    ∃ (P : Matrix (Fin n) (Fin m) ℝ) (f : Fin n → ℝ),
      CompOT.Assignment.IsOptimalCoupling C a b P ∧ CompOT.Assignment.frob C P = dualObj a b f (cTransform C f) ∧
      ∀ f' : Fin n → ℝ, dualObj a b f' (cTransform C f') ≤ dualObj a b f (cTransform C f) := by sorry

end CompOT.Duality
