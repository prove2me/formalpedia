-- Prove2me | Theorems.Thm_AggGameNet_Sync_lemma_4
-- name    : AggGameNet.Sync.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:23.265836+00:00
-- url     : https://prove2.me/theorems/797b37e6-e567-4474-9743-e020144412fe
-- title:
--   Lemma 4, p. 11 — explicit aggregate-estimate disagreement bound
-- statement:
--   Under the synchronous graph, weight and run assumptions, suppose the projected gradients have norm at most $C$ and $M$ bounds the sum of norms of every feasible profile. For each player $i$ and $k\ge1$,
--
--   $$\|y^k-\hat v_i^k\|\le\theta\beta^k M+\theta NC\sum_{s=1}^k\beta^{k-s}\alpha_{s-1},$$
--
--   where $\theta=(1-\delta/(4N^2))^{-2}$ and $\beta=(1-\delta/(4N^2))^{1/Q}$.
--
--   The estimate gives a quantitative effect of communication on local aggregate accuracy.
--
--   **Formalization Note** Nonnegative stepsizes are explicit because the displayed bound uses $\|x_i^{k+1}-x_i^k\|\le C\alpha_k$; they follow from Assumption 6 in the goal. Assumption 3 is extended to all aggregate arguments. The paper chooses $M=\sum_i\max_{x_i\in K_i}\|x_i\|$, the least bound in this formulation.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 4, pp. 11–12

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

/-- Lemma 4, p. 11: explicit bound for disagreement with the mean estimate. -/
theorem lemma_4 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (hα : ∀ k, 0 ≤ α k)
    (x v : ℕ → Fin N → E n)
    (hrun : IsSyncRun K F W α x v)
    (C : ℝ)
    (hC : ∀ i k, ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C)
    (M : ℝ)
    (hM : ∀ y : Fin N → E n, (∀ j, y j ∈ K j) → ∑ j, ‖y j‖ ≤ M) :
    ∀ i k, 1 ≤ k →
      ‖yavg v k - vhat W v k i‖ ≤
        theta N δ * beta N Q δ ^ k * M +
        theta N δ * (N : ℝ) * C *
          (∑ s ∈ Finset.Icc 1 k, beta N Q δ ^ (k - s) * α (s - 1)) := by sorry

end AggGameNet.Sync
