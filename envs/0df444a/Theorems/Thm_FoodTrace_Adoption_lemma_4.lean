-- Prove2me | Theorems.Thm_FoodTrace_Adoption_lemma_4
-- name    : FoodTrace.Adoption.lemma_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:26.539332+00:00
-- url     : https://prove2.me/theorems/08c8d016-bcbf-4320-8e9d-97010f688744
-- title:
--   Lemma 4 — with traceability tier-1 offers p^e_T for w ≥ w^e_T and p^o_T for w^o_T ≤ w < w^e_T
-- statement:
--   Consider Case T under the standing assumptions, with $w^o_T = p^o_T$ and
--   $$w^e_T = \frac{(1-\rho_e)e - \rho_\tau c_p}{\rho_\tau^2}.$$
--   Then $w^o_T = p^o_T < p^e_T < w^e_T$. A tier-2 response that plays the selected outcome at every procurement price exists, and for every such response tier-1 has a best response at every wholesale price. For every such tier-2 response and every tier-1 strategy that is a best response at every $w$, tier-1 offers $p^e_T$ when $w \ge w^e_T$ and $p^o_T$ when $w^o_T \le w < w^e_T$, and it transacts with the retailer if and only if $w \ge w^o_T$.
--
--   This is the second stage of the backward induction in Case T.
--
--   **Formalization Note** Best responses carry the tie rules of p. 8, as in Lemma 2.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 13, Lemma 4

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Lemma 4 (p. 13): tier-1's optimal procurement price with traceability. `w^o_T = p^o_T <
p^e_T < w^e_T`; a best response exists at every wholesale price; it offers `p^e_T` for
`w ≥ w^e_T` and `p^o_T` for `w^o_T ≤ w < w^e_T`; tier-1 transacts iff `w ≥ w^o_T`. -/
theorem lemma_4 (P : Params) (hP : Standing P) :
    wTo P = pTo P ∧ pTo P < pTe P ∧ pTe P < wTe P ∧
    (∃ σ₂ : ℝ → Option (Profile P), ∀ p, Tier2Selects .T P p (σ₂ p)) ∧
    (∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .T P p (σ₂ p)) →
      ∀ w : ℝ, ∃ x, IsTier1BR .T σ₂ w x) ∧
    ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .T P p (σ₂ p)) → (∀ w, IsTier1BR .T σ₂ w (σ₁ w)) →
      (∀ w : ℝ, wTe P ≤ w → σ₁ w = some (pTe P)) ∧
      (∀ w : ℝ, wTo P ≤ w → w < wTe P → σ₁ w = some (pTo P)) ∧
      (∀ w : ℝ, tier1Outcome σ₂ (σ₁ w) ≠ none ↔ wTo P ≤ w) := by sorry

end FoodTrace.Adoption
