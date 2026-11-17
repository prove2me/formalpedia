-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_E_11
-- name    : AggCG.Supplement.theorem_E_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:30:52.054788+00:00
-- url     : https://prove2.me/theorems/546ba085-e7ff-4867-b7d7-0900205f4a74
-- title:
--   Theorem E.11 — expected transitions of independent-edge minimum cuts
-- statement:
--   For a finite edge set $E$, fixed finite cut family, and independent distances supported on $[a,a+B]$ with densities at most $\kappa$, let $C_s$ minimize $\sum_{e\in C}e^{-sD_e}$ with deterministic tie breaking. If $N=|E|$, then the number $K$ of changes on $s\in(0,\infty)$ satisfies
--
--   $$
--   \mathbb EK\le\kappa BN\left(1+N\log N+\frac Ne\right)=O(\kappa BN^2\log(N+1)).
--   $$
--
--   For Gaussian graph weights $e^{-d_e^2/(2\sigma^2)}$ with independent $d_e\in[1,2]$ of density at most $\kappa_d$, this gives $\mathbb EK=O(\kappa_dn^4\log n)$ whenever $N=O(n^2)$, over all $\sigma>0$.
--
--   Differences from the source:
--   - encoding: the source takes an expectation of a finite transition count → Lean uses local nonconstancy, $\mathbb N\cup\{\infty\}$ cardinality, and a lower Lebesgue integral with measurability asserted; reason: this records the same transitions while preventing infinite or nonmeasurable counts from receiving a default finite value
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem E.11, p.34, PDF p.35

import Mathlib
import Definitions.Def_AggCG_Supplement_optimalCut
import Definitions.Def_AggCG_Supplement_changePoints
import Definitions.Def_AggCG_Supplement_BoundedDensityOn

namespace AggCG.Supplement

open MeasureTheory

/-- **Theorem E.11** (Whole-line expected transition bound for independent exponential edge weights;
Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), p.34, PDF p.35), in the model of
§E.4 (p.33): a finite edge set `E` with `N = |E|`, a fixed finite cut family `𝒞 ⊆ 2^E`, independent edge
distances `D_e` supported on `[a, a + B]` with densities at most `κ`, `W_C(s) = Σ_{e∈C} e^{−s D_e}` and
`C_s ∈ argmin_{C∈𝒞} W_C(s)` with deterministic tie breaking.
(1) The expected number `K` of changes of `C_s` on `s ∈ (0, ∞)` satisfies
`E K ≤ κBN(1 + N log N + N/e)`, and with one absolute constant `C`, `E K ≤ C κ B N² log(N + 1)`.
(2) For Gaussian weights `e^{−d_e²/(2σ²)}` with independent primitive distances `d_e ∈ [1, 2]` of densities
at most `κ_d`, on a graph with `n ≥ 2` vertices and `N ≤ n²` edges, the expected number of changes of the
optimal cut over all bandwidths `σ > 0` is at most `C κ_d n⁴ log n`, with one absolute constant `C`.

**Formalization Note** Expectations are lower Lebesgue integrals of `ℕ∞`-valued counts, with almost-sure
measurability of the count part of the claim. The tie rule depends only on the set of tied cuts. -/
theorem theorem_E_11 :
    (∀ (E : Type) [Fintype E] [DecidableEq E] (𝒞 : Finset (Finset E)) (tie : CutTieRule E)
      (a B κ : ℝ) (ν : E → Measure ℝ) [∀ e, IsProbabilityMeasure (ν e)],
      (∀ e, BoundedDensityOn (ν e) κ a (a + B)) →
      AEMeasurable (fun D : E → ℝ => ((changeCount (fun s => optimalCut 𝒞 tie fun e => Real.exp (-(s * D e)))
          (Set.Ioi 0) : ℕ∞) : ENNReal)) (Measure.pi ν) ∧
      ∫⁻ D, ((changeCount (fun s => optimalCut 𝒞 tie fun e => Real.exp (-(s * D e))) (Set.Ioi 0) : ℕ∞) :
          ENNReal) ∂(Measure.pi ν) ≤
        ENNReal.ofReal (κ * B * Fintype.card E *
          (1 + Fintype.card E * Real.log (Fintype.card E) + Fintype.card E / Real.exp 1))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (E : Type) [Fintype E] [DecidableEq E] (𝒞 : Finset (Finset E))
      (tie : CutTieRule E) (a B κ : ℝ) (ν : E → Measure ℝ) [∀ e, IsProbabilityMeasure (ν e)],
      (∀ e, BoundedDensityOn (ν e) κ a (a + B)) →
      ∫⁻ D, ((changeCount (fun s => optimalCut 𝒞 tie fun e => Real.exp (-(s * D e))) (Set.Ioi 0) : ℕ∞) :
          ENNReal) ∂(Measure.pi ν) ≤
        ENNReal.ofReal (C * κ * B * (Fintype.card E : ℝ) ^ 2 * Real.log (Fintype.card E + 1))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (E : Type) [Fintype E] [DecidableEq E],
      Fintype.card E ≤ n ^ 2 → ∀ (𝒞 : Finset (Finset E)) (tie : CutTieRule E) (κd : ℝ)
      (ν : E → Measure ℝ) [∀ e, IsProbabilityMeasure (ν e)], (∀ e, BoundedDensityOn (ν e) κd 1 2) →
      ∫⁻ d, ((changeCount (fun σ => optimalCut 𝒞 tie fun e => Real.exp (-(d e ^ 2 / (2 * σ ^ 2))))
          (Set.Ioi 0) : ℕ∞) : ENNReal) ∂(Measure.pi ν) ≤
        ENNReal.ofReal (C * κd * (n : ℝ) ^ 4 * Real.log n)) := by sorry

end AggCG.Supplement
