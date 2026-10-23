-- Prove2me | Theorems.Thm_FoodTrace_Adoption_lemma_3
-- name    : FoodTrace.Adoption.lemma_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:15.724982+00:00
-- url     : https://prove2.me/theorems/62407748-62c6-4f87-982e-a15218d7ac42
-- title:
--   Lemma 3 — with traceability the tier-2 equilibrium effort outcome is symmetric, with thresholds p^o_T < p^e_T
-- statement:
--   Consider the supply chain with traceability (Case T) under the standing assumptions, with
--   $$p^o_T = \frac{c_p}{1-\rho}, \qquad p^e_T = \frac{e}{\rho_\tau}.$$
--   Then $p^o_T < p^e_T$, and:
--
--   1. Every viable tier-2 equilibrium at any procurement price is symmetric.
--   2. For $p \ge p^e_T$ the selected outcome is the all-effort profile; for $p^o_T \le p < p^e_T$ it is the no-effort profile.
--   3. At every $p$ a selected outcome exists, and the farms sell to tier-1 if and only if $p \ge p^o_T$.
--
--   This is the first stage of the backward induction in Case T.
--
--   **Formalization Note** As in Lemma 1, "the selected outcome is $X$" is stated as an equivalence, which gives existence and uniqueness.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 13, Lemma 3

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Lemma 3 (p. 13): with traceability `p^o_T < p^e_T`, every viable tier-2 equilibrium is
symmetric, the selected outcome is all-effort for `p ≥ p^e_T` and no-effort for
`p^o_T ≤ p < p^e_T`, and tier-2 sells iff `p ≥ p^o_T`. -/
theorem lemma_3 (P : Params) (hP : Standing P) :
    pTo P < pTe P ∧
    (∀ (p : ℝ) (a : Profile P), IsViableEq .T P p a → (∀ i, a i = true) ∨ (∀ i, a i = false)) ∧
    (∀ p : ℝ, pTe P ≤ p → ∀ o, Tier2Selects .T P p o ↔ o = some (allEffort P)) ∧
    (∀ p : ℝ, pTo P ≤ p → p < pTe P → ∀ o, Tier2Selects .T P p o ↔ o = some (noEffort P)) ∧
    (∀ p : ℝ, (∃ o, Tier2Selects .T P p o) ∧
      ∀ o, Tier2Selects .T P p o → (o ≠ none ↔ pTo P ≤ p)) := by sorry

end FoodTrace.Adoption
