-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_8
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:33.416393+00:00
-- url     : https://prove2.me/theorems/fead71a0-0a85-4bab-aa59-81f17a950582
-- title:
--   Lemma 8 — layer-cake formula for the maximum-weight independent set
-- statement:
--   Let $\mathcal M$ be a matroid on a finite set $V_C$ with rank function $r$, and let $z\in\mathbb R^{V_C}$ be an arbitrary real weight vector (negative coordinates allowed). Then
--
--   $$\max_{I\in\mathcal I}\sum_{j\in I}z_j=\int_0^\infty r\big(\{j\in V_C:z_j\ge t\}\big)\,dt.\tag{5}$$
--
--   This is Theorem 40.2 of Schrijver's *Combinatorial Optimization* in integral form; applied to $z_j=p_j-d(j,i)$ it shows that the facility terms of (2) are monotone and supermodular in the dual vector.
--
--   **Formalization Note** Both sides are nonnegative (the empty set is independent), so the identity is stated in $[0,\infty]$: the left side through `ENNReal.ofReal`, the right side as the Lebesgue integral of the extended-natural rank `eRk` over $(0,\infty)$, which needs no integrability hypothesis.
--
--   Differences from the source:
--   - generalization: the matroid M = (V_C, ℐ) on exactly the clients → any matroid M on the finite type C (its ground set need not be all of C); reason: independent sets and ranks of superlevel sets only see the ground set; the source's case is ground = C
--   - encoding: real identity with an improper integral ∫_0^∞ r(·) dt → ENNReal.ofReal of the left side equals the lower Lebesgue integral over (0,∞) of the ℕ∞-valued rank eRk; reason: both sides are nonnegative and the integrand is a bounded nonnegative step function, so the two integrals agree; the endpoint 0 has measure zero
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 8 (Theorem 40.2 in [Sch03]), eq. (5), printed p.7 / PDF p.8

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Model

open scoped ENNReal
open MeasureTheory

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 8** (Theorem 40.2 in [Sch03]; printed p.7 / PDF p.8), equation (5): for every real
weight vector `z`, `max_{I ∈ ℐ} ∑_{j ∈ I} z_j = ∫_0^∞ r({j ∈ V_C : z_j ≥ t}) dt`. -/
theorem lemma_8 {C : Type*} [Fintype C] (M : Matroid C) (z : C → ℝ) :
    ENNReal.ofReal (matroidMaxWeight M z) =
      ∫⁻ t in Set.Ioi (0 : ℝ), ((M.eRk {j | t ≤ z j} : ℕ∞) : ℝ≥0∞) := by sorry

end FacilityIncompatibilities.UniformMatroid
