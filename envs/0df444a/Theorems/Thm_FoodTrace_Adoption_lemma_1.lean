-- Prove2me | Theorems.Thm_FoodTrace_Adoption_lemma_1
-- name    : FoodTrace.Adoption.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:15.055875+00:00
-- url     : https://prove2.me/theorems/4a6c715c-0469-4495-afed-47f2a6e2f589
-- title:
--   Lemma 1 — without traceability the tier-2 equilibrium effort portfolio is symmetric, with thresholds p^o_N, p^e_N
-- statement:
--   Consider the supply chain without traceability (Case N) under the standing assumptions ($n \ge 2$, $0 \le \rho_e < \rho < 1$, $e > 0$, $0 < c_p < \bar c_p$). Let
--   $$\underline c_p = \frac{e(1-\rho)^n}{\rho_\tau(1-\rho_e)^{n-1}}, \qquad p^o_N = \frac{c_p}{(1-\rho)^n}, \qquad p^e_N = \frac{e}{\rho_\tau(1-\rho_e)^{n-1}}.$$
--   Then:
--
--   1. Every viable tier-2 equilibrium at any procurement price $p$ is symmetric: all farms exert effort or none does.
--   2. If $c_p < \underline c_p$, then $p^o_N < p^e_N$; for $p \ge p^e_N$ the selected (Pareto-dominant) outcome is the all-effort profile, and for $p^o_N \le p < p^e_N$ it is the no-effort profile.
--   3. If $\underline c_p \le c_p$, then $p^o_N \ge p^e_N$, and for $p \ge p^e_N$ the selected outcome is the all-effort profile.
--   4. At every $p$ a selected outcome exists, and the farms sell to tier-1 if and only if $p \ge \min\{p^e_N, p^o_N\}$.
--
--   This is the first stage of the backward induction in Case N; Lemma 2 and Proposition 1 build on it.
--
--   **Formalization Note** "The selected outcome is $X$" is stated as: the selection relation holds for an outcome if and only if it is $X$, which gives existence and uniqueness. Symmetry (item 1) is stated for every viable equilibrium, not only the selected one.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 9, Lemma 1

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Lemma 1 (p. 9): without traceability every viable tier-2 equilibrium is symmetric (all effort
or none); the selected outcome is all-effort for `p ≥ p^e_N` and, when `0 < c_p < c̲_p`, no-effort
for `p^o_N ≤ p < p^e_N`; tier-2 sells iff `p ≥ min{p^e_N, p^o_N}`. -/
theorem lemma_1 (P : Params) (hP : Standing P) :
    (∀ (p : ℝ) (a : Profile P), IsViableEq .N P p a → (∀ i, a i = true) ∨ (∀ i, a i = false)) ∧
    (P.cp < cpLow P → pNo P < pNe P ∧
      (∀ p : ℝ, pNe P ≤ p → ∀ o, Tier2Selects .N P p o ↔ o = some (allEffort P)) ∧
      (∀ p : ℝ, pNo P ≤ p → p < pNe P → ∀ o, Tier2Selects .N P p o ↔ o = some (noEffort P))) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧
      (∀ p : ℝ, pNe P ≤ p → ∀ o, Tier2Selects .N P p o ↔ o = some (allEffort P))) ∧
    (∀ p : ℝ, (∃ o, Tier2Selects .N P p o) ∧
      ∀ o, Tier2Selects .N P p o → (o ≠ none ↔ min (pNe P) (pNo P) ≤ p)) := by sorry

end FoodTrace.Adoption
