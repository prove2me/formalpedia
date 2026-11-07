-- Prove2me | Theorems.Thm_FairKMeans_lemma_19
-- name    : FairKMeans.lemma_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:33:07.010404+00:00
-- url     : https://prove2.me/theorems/bd0eaf94-0faf-458e-80d9-249663573d56
-- title:
--   Lemma 19 — fair routing: whole columns rerouted to $S$ cost $C_T+\mathrm{Cost}(\pi(T),S)$
-- statement:
--   Let $(T,\phi_T)$ be a relaxed solution and $S$ a nonempty center family. Then:
--
--   1. the fair assignment LP of $S$ has a feasible solution;
--   2. every optimal solution $\phi^*_S$ of it satisfies $\mathrm{Cost}(P,S,\phi^*_S)\le C_T+\mathrm{Cost}(\pi(T),S)$, where $\pi(T)$ is the family of centroids $\pi(t)$ with weights $w(t)$;
--   3. $C_T\le\mathrm{Cost}(P,T,\phi_T)$.
--
--   This bounds the cost of the final solution by the $k$-means cost of the weighted centroids.
--
--   Differences from the source:
--   - encoding: a center set S → a family with at least one center; reason: Cost(π(T), ∅) = +∞ in the paper and the proof routes every column to a nearest center of S
--   - reading: its optimal solution ϕ*_S satisfies → every optimal solution satisfies; reason: the LP may have several optima; the proof applies to each
--   - encoding: π(t) of a zero column (undefined) → Lean's 0⁻¹ • 0 = 0, always multiplied by the weight 0; reason: Lean convention; no sum changes
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Lemma 19, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-- **Lemma 19 (Fair routing)**, p.26 (PDF 28). Cheng–Mo–Song–Ding, arXiv:2609.07974 (held
version, sha256 73e9312c…).

For a relaxed solution `(T, φ_T)` and a (nonempty) center set `S`, the fair assignment LP of `S`
has a feasible solution, every optimal solution `φ*_S` satisfies
`Cost(P, S, φ*_S) ≤ C_T + Cost(π(T), S)`, where `π(T)` carries the weights `w(t)`, and
`C_T ≤ Cost(P, T, φ_T)`.

**Formalization Note.** `S` has at least one center: the proof sends every column to a nearest
center of `S`, and the paper's `Cost(π(T), ∅)` is `+∞`. -/
theorem lemma_19 {d n m s sS : ℕ} (I : Instance d n m) (T : Fin s → E d)
    (φ : Fin n → Fin s → ℝ) (h : IsRelaxed I φ) (S : Fin sS → E d) (hS : 1 ≤ sS) :
    (∃ ψ : Fin n → Fin sS → ℝ, IsAssignment ψ ∧ IsFair I ψ) ∧
      (∀ ψ : Fin n → Fin sS → ℝ, IsOptFairAssign I S ψ →
        cost I S ψ ≤ CT I φ + kmCost (cen I φ) (clusterWeight φ) S) ∧
      CT I φ ≤ cost I T φ := by sorry

end FairKMeans
