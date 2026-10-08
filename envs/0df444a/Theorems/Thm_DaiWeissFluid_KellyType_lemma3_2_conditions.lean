-- Prove2me | Theorems.Thm_DaiWeissFluid_KellyType_lemma3_2_conditions
-- name    : DaiWeissFluid.KellyType.lemma3_2_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:22:23.98954+00:00
-- url     : https://prove2.me/theorems/3e3e7ee4-5eed-4272-a3c9-cc3292093dd8
-- title:
--   Proof of Theorem 6.1 — the components G₁, G₂ satisfy the conditions of Lemma 3.2
-- statement:
--   Let a two-station reentrant line be of Kelly type with station means $\beta_1, \beta_2$, have no immediate feedback, positive mean service times, and satisfy the traffic condition (1.7), $\rho_i = |C_i|\,\beta_i < 1$. Let $(Q,T)$ be a work-conserving fluid model solution, (1.8)–(1.13), and write the Lyapunov components as
--
--   $$ G_i(t) = \sum_{k\in C_i} Q^+_k(t) = \sum_{l=1}^K c_{i,l}\,Q_l(t), \qquad c_{i,l} = \#\{k \in C_i : l \le k\}. $$
--
--   Then, with $\varepsilon_i = 1/\beta_i - |C_i|$:
--
--   1. $\varepsilon_i > 0$ for every station $i$ that serves at least one class;
--   2. condition (a) of Lemma 3.2: for $t > 0$ with $W_i(t) > 0$, every derivative of $G_i$ at $t$ is $\le -\varepsilon_i$;
--   3. condition (b) of Lemma 3.2: for $t \ge 0$, $W_i(t) = 0$ implies $G_i(t) \le G_j(t)$ for $j \ne i$.
--
--   This is the step "one can check that all conditions in Lemma 3.2 on $G_1(t)$ and $G_2(t)$ are satisfied" of the proof of Theorem 6.1. For $K = 2n$, (1.7) reads $n\beta_i < 1$, the paper's (6.1).
--
--   **Formalization Note** A station with no classes has $W_i \equiv 0$, so (a) is vacuous there and its $\beta_i$ is unconstrained; item 1 is therefore stated only for visited stations, and a solver applying Lemma 3.2 may take $\varepsilon_i = 1$ at an unvisited station. Both parities of $K$ and both starting stations are covered. Indices are 0-based.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 130, proof of Theorem 6.1 ("One can check that all conditions in Lemma 3.2 …"), (6.1)

import Mathlib
import Definitions.Def_DaiWeissFluid_KellyType_FluidModel
import Definitions.Def_DaiWeissFluid_KellyType_KellyLine

namespace DaiWeissFluid.KellyType

/-- Proof of Theorem 6.1, p. 130 ("one can check that all conditions in Lemma 3.2 on `G₁(t)` and
`G₂(t)` are satisfied"): for every work-conserving fluid solution of a two-station Kelly-type
reentrant line without immediate feedback under (1.7), the components
`G_i(t) = ∑_l c_{i,l} Q_l(t)`, `c_{i,l} = #{k ∈ C_i : l ≤ k}`, satisfy
1. `ε_i = 1/β_i - |C_i| > 0` at every visited station `i`;
2. condition (a) of Lemma 3.2 with this `ε_i`: at `t > 0` with `W_i(t) > 0`, every derivative of
   `G_i` at `t` is `≤ -ε_i`;
3. condition (b) of Lemma 3.2: `W_i(t) = 0` implies `G_i(t) ≤ G_j(t)` for `j ≠ i`. -/
theorem lemma3_2_conditions {K : ℕ} (L : ReentrantLine 2 K) (hm : ∀ k, 0 < L.m k)
    (hρ : ∀ i, L.ρ i < 1) (β : Fin 2 → ℝ) (hkelly : L.IsKellyType β)
    (hfb : L.NoImmediateFeedback)
    (Q T : ℝ → Fin K → ℝ) (hwc : L.IsWorkConserving Q T) :
    (∀ i, (L.C i).Nonempty → 0 < (β i)⁻¹ - ((L.C i).card : ℝ)) ∧
    (∀ i t, 0 < t → 0 < L.volume Q i t →
      ∀ d, HasDerivAt (fun s => ∑ k, L.kellyCoeff i k * Q s k) d t →
        d ≤ -((β i)⁻¹ - ((L.C i).card : ℝ))) ∧
    (∀ i t, 0 ≤ t → L.volume Q i t = 0 →
      ∀ j, j ≠ i → ∑ k, L.kellyCoeff i k * Q t k ≤ ∑ k, L.kellyCoeff j k * Q t k) := by sorry

end DaiWeissFluid.KellyType
