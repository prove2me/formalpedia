-- Prove2me | Theorems.Thm_DurrettProbability_donsker_max
-- name    : DurrettProbability.donsker_max
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-19T02:16:22.611582+00:00
-- url     : https://prove2.me/theorems/44534506-ff52-4218-a77f-6664bcc308f5
-- title:
--   Example 8.1.6 — the maximum of the walk converges to the maximum of Brownian motion
-- statement:
--   Under the hypotheses of Durrett's Theorem 8.1.2 — $X_0,X_1,\dots$ measurable, jointly
--   independent, identically distributed, with mean $0$ and variance $1$ — and with $B$ a Brownian
--   motion all of whose paths are continuous,
--   $$\max_{0\le m\le n}\frac{S_m}{\sqrt n}\ \Longrightarrow\ \max_{0\le t\le1}B_t ,$$
--   where $S_m=X_0+\dots+X_{m-1}$, so that the maximum on the left includes $S_0=0$, and the right
--   side is the supremum of the Brownian path over the unit interval.
--
--   **Formalization Note** The left side is the maximum of $S_m/\sqrt n$ over the $n+1$ indices
--   $0\le m\le n$, taken as a maximum over a non-empty finite set. At $n=0$ the rescaling divides by
--   $\sqrt0=0$, which in the reals is $0$; this has no effect on a limit along $n\to\infty$.
--
--   The right side is the supremum of $t\mapsto B_t(\omega)$ over $[0,1]$, written as a supremum in
--   the reals. Because the path is continuous and the interval is compact and non-empty, this
--   supremum is attained and is the maximum the book writes; no separate boundedness hypothesis is
--   needed.
--
--   Both sides are non-negative, since $m=0$ and $t=0$ contribute $0$. Durrett's companion formula
--   $\mathbb P(M_1\ge a)=2\,\mathbb P(B_1\ge a)$, which identifies the limit law through the
--   reflection principle, is not part of this statement.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 392 (PDF p. 400), Example 8.1.6: 'Maxima. Let psi(omega) = max{omega(t) : 0 <= t <= 1}. Again, psi : C[0,1] -> R is continuous. This time Theorem 8.1.5 implies max_{0 <= m <= n} S_m/sqrt(n) => M_1 = max_{0 <= t <= 1} B_t. To complete the picture, we observe that by (7.4.4) the distribution of the right-hand side is P_0(M_1 >= a) = P_0(T_a <= 1) = 2 P_0(B_1 >= a).' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_DurrettProbability_Donsker

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem donsker_max
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hmeas : ∀ k, Measurable (X k)) (hindep : iIndepFun X P)
    (hident : ∀ k, IdentDistrib (X k) (X 0) P P) (hint : Integrable (fun ω => X 0 ω ^ 2) P)
    (hmean : ∫ ω, X 0 ω ∂P = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂P = 1)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous fun t => B t ω) :
    TendstoInDistribution
      (fun n : ℕ => fun ω => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun m => (∑ k ∈ Finset.range m, X k ω) / Real.sqrt n)
      atTop
      (fun ω => ⨆ t : Set.Icc (0 : ℝ) 1, B ⟨t, t.2.1⟩ ω) (fun _ => P) P' := by sorry

end DurrettProbability
