-- Prove2me | Theorems.Thm_CatalyticRD_crd2_solution_pos
-- name    : CatalyticRD.crd2_solution_pos
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T18:17:55.526649+00:00
-- url     : https://prove2.me/theorems/4cccc646-70ac-4459-a024-5a6f423388c5
-- title:
--   Positivity of solutions of the catalytic reaction–diffusion system
-- statement:
--   Let $\Omega=\{\varphi<0\}\subset\mathbb R^n$ be a smooth bounded connected domain with $|\Omega|=1$, $d_1,d_2,d_3>0$, and let $(a,b,c)$ be a classical solution of the catalytic system (Nguyen–Tang, eq. (1.1))
--
--   $$\partial_t a-d_1\Delta a=b(c-a),\quad \partial_t b-d_2\Delta b=b(c-a),\quad \partial_t c-d_3\Delta c=-b(c-a)$$
--
--   with homogeneous Neumann conditions and admissible initial data $a_0,b_0,c_0$ ($C^2(\overline\Omega)$, strictly positive on $\overline\Omega$, Neumann-compatible), all as in `CatalyticRD_Setup`. Then
--
--   $$a(t,x)>0,\quad b(t,x)>0,\quad c(t,x)>0\qquad\text{for all }t\ge0,\ x\in\overline\Omega.$$
--
--   Positivity is claimed up to the boundary, not only in $\Omega$.
--
--   **Formalization Note** The hypothesis $|\Omega|=1$ is not needed; it is kept so the signature matches the main theorem.
-- source:
--   Strong parabolic maximum principle and boundary-point (Hopf) lemma, applied to weakly coupled systems with quasi-positive reaction terms: M. H. Protter and H. F. Weinberger, Maximum Principles in Differential Equations, Springer (1984), Ch. 3; G. M. Lieberman, Second Order Parabolic Differential Equations, World Scientific (1996), Ch. II. System and setting: T. L. Nguyen and B. Q. Tang, Z. Angew. Math. Phys. 77 (2026) 199, eq. (1.1) and Theorem 2.1.

import Mathlib
import Definitions.Def_CatalyticRD_Setup

open MeasureTheory Set Filter Topology

namespace CatalyticRD

theorem crd2_solution_pos {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hΩ : IsSmoothBoundedDomain Ω φ) (hvol : volume Ω = 1)
    (d₁ d₂ d₃ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hd₃ : 0 < d₃)
    (a₀ b₀ c₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha₀ : IsAdmissibleDatum Ω φ a₀) (hb₀ : IsAdmissibleDatum Ω φ b₀)
    (hc₀ : IsAdmissibleDatum Ω φ c₀)
    (a b c : ℝ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hsol : IsClassicalSolution Ω φ d₁ d₂ d₃ a₀ b₀ c₀ a b c) :
    ∀ t ≥ 0, ∀ x ∈ closure Ω, 0 < a t x ∧ 0 < b t x ∧ 0 < c t x := by sorry

end CatalyticRD
