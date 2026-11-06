-- Prove2me | Theorems.Thm_FlexibleNRM_vfa_zero
-- name    : FlexibleNRM.vfa_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:26:59.212992+00:00
-- url     : https://prove2.me/theorems/54fc242e-94a6-4fc9-8c58-0d345e13f8fc
-- title:
--   Proof of Theorem 4.1, p.18 — $\hat J_t(0)=\sum_j\sum_{p\in\mathcal R_j}\hat\gamma_{jpt}$
-- statement:
--   At the empty state the only feasible solution of (3) has $w=c$, and $\psi_p(c)=1$, so
--   $$\hat J_t(0)=\sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}\hat\gamma_{jpt}.$$
--   At $t=1$ this connects the two steps of the performance guarantee.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: Ĵ_t(x) is a max over (y, w), Eq. (3) → vfa is the sSup of the attained values, with junk value 0 when F(x) = ∅; reason: the set of values is finite, so at feasible x the sSup is the max; the junk value is read only under the indicator of F(x + e_j) ≠ ∅, where it is multiplied by 0
--   - generalization: Ĵ_1(0) for the parameters of the algorithm → Ĵ_t(0) for every t and arbitrary real parameters; reason: the step reads neither the calibration nor the period, and t = 1 with the calibrated parameters is an instance
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, proof of Theorem 4.1, p.18

import Mathlib
import Definitions.Def_FlexibleNRM_vfa

namespace FlexibleNRM

/-- **The approximation at the empty state**: `Ĵ_t(0) = ∑_j ∑_{p ∈ R_j} γ̂_jpt`.

Zhu, Topaloglu, manuscript of November 16, 2022, proof of Theorem 4.1, p.18 (at `t = 1`).

**Formalization Note** The paper's step at `t = 1` reads neither the calibration nor the period, so
`γ` and `t` are arbitrary. -/
theorem vfa_zero {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ) (t : ℕ) :
    vfa N γ t 0 = ∑ j, ∑ p ∈ N.R j, γ j p t := by sorry

end FlexibleNRM
