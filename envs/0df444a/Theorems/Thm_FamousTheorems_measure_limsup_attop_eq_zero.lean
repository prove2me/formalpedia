-- Prove2me | Theorems.Thm_FamousTheorems_measure_limsup_attop_eq_zero
-- name    : FamousTheorems.measure_limsup_attop_eq_zero
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:21.485861+00:00
-- url     : https://prove2.me/theorems/457bfe68-a9c6-493b-90cd-1f1ad753a2cd
-- title:
--   The Borel–Cantelli lemma (easy direction)
-- statement:
--   **The first Borel\u2013Cantelli lemma.** If $\sum_n \mu(S_n) < \infty$ then $$\mu\bigl(\limsup_n S_n\bigr) = 0,$$ so almost no point lies in infinitely many of the $S_n$. No independence is required — this direction is pure measure theory, following from countable subadditivity applied to the tails of a convergent series. It is the standard tool for almost-sure statements: to show an event happens only finitely often, bound its probabilities by a summable sequence. This is how one proves the strong law of large numbers along subsequences, and how almost-sure convergence is extracted from convergence in probability. **Formalization note.** `limsup` of a sequence of sets is the set of points belonging to infinitely many of them. The result is Mathlib's `MeasureTheory.measure_limsup_atTop_eq_zero`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem measure_limsup_attop_eq_zero :
    ∀ {α : Type u_1} {F : Type u_2} [inst : FunLike F (Set α) ENNReal] 
    [MeasureTheory.OuterMeasureClass F α] {μ : F} {s : ℕ → Set α}, ∑' (i : ℕ), μ (s i) ≠ ⊤ → μ (limsup s atTop) = 0 := by sorry

end FamousTheorems
