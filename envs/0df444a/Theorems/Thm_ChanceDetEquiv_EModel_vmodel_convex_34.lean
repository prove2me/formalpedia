-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_vmodel_convex_34
-- name    : ChanceDetEquiv.EModel.vmodel_convex_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:13.304666+00:00
-- url     : https://prove2.me/theorems/e22b7839-64bf-4f3c-9c79-8df9dc68bcd8
-- title:
--   'V Model' (32)–(34), p. 30 — the chance constraints have the convex equivalent (33) and V(D) is convex
-- statement:
--   Assume every $b_k$ and every product $c_jb_k$ is square integrable, each variate $a_i'Db-b_i$ is normal for every decision rule $D$, and $\tfrac12<\alpha_i<1$. Let $z^0=c^{0\prime}x^0$ be a given real number. The V-model (32) uses the chance constraints $P(a_i'Db\le b_i)\ge\alpha_i$ and the functional
--   $$V(D)=E\big(c'Db-z^0\big)^2.\qquad(34)$$
--   For every $D$, those chance constraints hold if and only if some $v$ makes $(D,v)$ satisfy the corrected system (33), namely the system (29). Its set of pairs $(D,v)$ is convex, and $V$ is a convex function of $D$. Thus (33)–(34) is the convex deterministic equivalent of (32).
--
--   **Formalization Note** The paper prints $K_{\alpha_i}\mu_i^2(D)$ in (33) for $K_{\alpha_i}^2\mu_i^2(D)$ and says the constraint sets are "the same as for (30)", meaning (29). The Lean uses (29), which gives the equivalence claimed by the surrounding text. Zero-variance normal laws are allowed.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 30, Eqs. (33)–(34)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **'V Model' (32)–(34)**, p. 30: under the E-model assumptions and square integrability
of each product `c_j b_k`, the chance constraints of (32) are equivalent to the constraints
of (33) for some `v`; those constraints define a convex set, and the functional
`V(D) = E(c'Db − z⁰)²` of (34) is convex in `D`, for any given `z⁰ = c⁰'x⁰`.
The second constraint of (33) uses the squared coefficient from (29), as the prose says
that the two systems have the same constraints. -/
theorem vmodel_convex_34 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ) (α : Fin m → ℝ)
    (hb : ∀ k, MemLp (fun ω => b ω k) 2 P)
    (hcb : ∀ j k, MemLp (fun ω => c ω j * b ω k) 2 P)
    (hnormal : RowsNormal P A b)
    (hα_lo : ∀ i, 1 / 2 < α i) (hα_hi : ∀ i, α i < 1) (z0 : ℝ) :
    (∀ D : Matrix (Fin n) (Fin m) ℝ, IsChanceFeasible18 P A b α D ↔ ∃ v, Sys29 P A b α D v) ∧
    Convex ℝ {p : Matrix (Fin n) (Fin m) ℝ × (Fin m → ℝ) | Sys29 P A b α p.1 p.2} ∧
    ConvexOn ℝ Set.univ (fun D : Matrix (Fin n) (Fin m) ℝ => VObjective P b c z0 D) := by sorry

end ChanceDetEquiv.EModel
