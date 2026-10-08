-- Prove2me | Theorems.Thm_FastFashion_Structure_delta_hA_monotone
-- name    : FastFashion.Structure.delta_hA_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:55.398002+00:00
-- url     : https://prove2.me/theorems/d20e9539-a060-44bf-a0fe-ade094b7cff4
-- title:
--   Appendix §5.1 — $\Delta_s h^{\mathcal A}(q)$ is non-increasing in $q_s$ and non-decreasing in $q_{s'}$, $s' \ne s$
-- statement:
--   Let $(N_s)_{s \in \mathcal S}$ be an independent Poisson family with rates $\lambda_s > 0$ on a probability space, let $T > 0$ and let $\mathcal A \subseteq \mathcal S$ be any set of sizes. Then for every $q \in \mathbb N^{\mathcal S}$ and all sizes $s, s'$ with $s \ne s'$,
--   $$\Delta_s h^{\mathcal A}(q + e_s) \le \Delta_s h^{\mathcal A}(q) \qquad\text{and}\qquad \Delta_s h^{\mathcal A}(q) \le \Delta_s h^{\mathcal A}(q + e_{s'}).$$
--   In particular $h^{\mathcal A}$ is discretely concave in each variable $q_s$, and its marginal differences in $q_s$ increase with the inventory of every other size.
--
--   These are the two marginal-difference properties of Proposition 1, proved first for every $h^{\mathcal A}$ and then transferred to $g_\lambda$ through identity (2).
--
--   **Formalization Note** The paper says "decreasing" and "increasing"; both are meant in the weak sense, as in Proposition 1. The statement is made for every size $s$; for $s \notin \mathcal A$ both sides are $0$.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 31, Appendix §5.1, Proof of Proposition 1, sentence after the display

import Mathlib
import Definitions.Def_FastFashion_Structure_Model

namespace FastFashion.Structure

open MeasureTheory ProbabilityTheory

theorem delta_hA_monotone {S Ω : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (lam : S → ℝ) (N : S → ℝ → Ω → ℕ) (T : ℝ)
    (hN : IsPoissonFamily lam N P) (hlam : ∀ s, 0 < lam s) (hT : 0 < T)
    (A : Finset S) :
    (∀ (q : S → ℕ) (s : S),
      delta (hA N P T A) s (q + Pi.single s 1) ≤ delta (hA N P T A) s q) ∧
    (∀ (q : S → ℕ) (s s' : S), s ≠ s' →
      delta (hA N P T A) s q ≤ delta (hA N P T A) s (q + Pi.single s' 1)) := by sorry

end FastFashion.Structure
