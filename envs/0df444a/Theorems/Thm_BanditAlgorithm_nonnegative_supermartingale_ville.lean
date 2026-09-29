-- Prove2me | Theorems.Thm_BanditAlgorithm_nonnegative_supermartingale_ville
-- name    : BanditAlgorithm.nonnegative_supermartingale_ville
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T14:27:27.409155+00:00
-- url     : https://prove2.me/theorems/f9620c13-f4b3-491d-9d7c-30a33356523a
-- title:
--   Ville's inequality for nonnegative supermartingales
-- statement:
--   Let $(M_t)_{t\ge 0}$ be a real-valued supermartingale on a probability space, adapted to a discrete-time filtration. Assume that $M_t\ge 0$ almost surely for every $t$ and that $M_0\le 1$ almost surely. Then, for every $\delta\in(0,1)$,
--
--   $$
--   \mathbb P\!\left(\exists t\in\mathbb N:\ M_t\ge\frac{1}{\delta}\right)\le\delta.
--   $$
--
--   This is Ville's inequality, or the maximal inequality for nonnegative supermartingales. Its time-uniform form is the probability-theoretic step that turns the mixture supermartingale in the self-normalized concentration argument into a bound valid simultaneously at every time.
--
--   **Formalization Note** Nonnegativity and the initial bound are stated almost surely, matching the measure-theoretic definition of a supermartingale.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), printed p. 51, Theorem 3.9 (Maximal inequality), used in the proof of Theorem 20.4 on printed p. 260, Eq. (20.7).

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.nonnegative_supermartingale_ville
    {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (f : ℕ → Ω → ℝ)
    (hf : Supermartingale f ℱ P)
    (hnonneg : ∀ t : ℕ, 0 ≤ᵐ[P] f t)
    (h0 : ∀ᵐ ω ∂P, f 0 ω ≤ 1)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | ∃ t : ℕ, 1 / δ ≤ f t ω} ≤ δ := by
  sorry
