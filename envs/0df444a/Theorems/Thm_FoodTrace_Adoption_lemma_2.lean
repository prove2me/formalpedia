-- Prove2me | Theorems.Thm_FoodTrace_Adoption_lemma_2
-- name    : FoodTrace.Adoption.lemma_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:23.982714+00:00
-- url     : https://prove2.me/theorems/1473b5e1-9cea-4f16-b39c-008c476336a2
-- title:
--   Lemma 2 — without traceability tier-1 offers p^e_N for w ≥ w^e_N and p^o_N for w^o_N ≤ w < w^e_N
-- statement:
--   Consider Case N under the standing assumptions, with $\ell = (1-\rho_e)^n - (1-\rho)^n$, $w^o_N = p^o_N$ and
--   $$w^e_N = \max\Big\{\frac{(1-\rho_e)e - \rho_\tau c_p}{\rho_\tau\,\ell},\; p^e_N\Big\}.$$
--   If $c_p < \underline c_p$, then $p^o_N < p^e_N < w^e_N$; if $\underline c_p \le c_p$, then $p^o_N \ge p^e_N = w^e_N$. A tier-2 response that plays the selected outcome at every procurement price exists, and for every such response tier-1 has a best response at every wholesale price $w$. For every such tier-2 response and every tier-1 strategy that is a best response at every $w$:
--
--   1. If $c_p < \underline c_p$, tier-1 offers $p^e_N$ when $w \ge w^e_N$ and $p^o_N$ when $w^o_N \le w < w^e_N$.
--   2. If $\underline c_p \le c_p$, tier-1 offers $p^e_N$ when $w \ge w^e_N$.
--   3. Tier-1 sells to the retailer (it offers a price and the farms sell) if and only if $w \ge \min\{w^e_N, w^o_N\}$.
--
--   This is the second stage of the backward induction in Case N.
--
--   **Formalization Note** A best response maximizes tier-1's profit over every $p \in \mathbb R$ and over not trading; among maximizers it induces effort whenever some maximizer does and trades whenever some maximizer trades (the rules of p. 8).
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), p. 10, Lemma 2

import Mathlib
import Definitions.Def_FoodTrace_Adoption_Model

namespace FoodTrace.Adoption

/-- Lemma 2 (p. 10): tier-1's optimal procurement price without traceability. A best response
exists at every wholesale price; it offers `p^e_N` for `w ≥ w^e_N` and, when `0 < c_p < c̲_p`,
`p^o_N` for `w^o_N ≤ w < w^e_N`; tier-1 sells iff `w ≥ min{w^e_N, w^o_N}`. -/
theorem lemma_2 (P : Params) (hP : Standing P) :
    (P.cp < cpLow P → pNo P < pNe P ∧ pNe P < wNe P) ∧
    (cpLow P ≤ P.cp → pNe P ≤ pNo P ∧ pNe P = wNe P) ∧
    (∃ σ₂ : ℝ → Option (Profile P), ∀ p, Tier2Selects .N P p (σ₂ p)) ∧
    (∀ σ₂ : ℝ → Option (Profile P), (∀ p, Tier2Selects .N P p (σ₂ p)) →
      ∀ w : ℝ, ∃ x, IsTier1BR .N σ₂ w x) ∧
    ∀ (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ),
      (∀ p, Tier2Selects .N P p (σ₂ p)) → (∀ w, IsTier1BR .N σ₂ w (σ₁ w)) →
      (P.cp < cpLow P →
        (∀ w : ℝ, wNe P ≤ w → σ₁ w = some (pNe P)) ∧
        (∀ w : ℝ, wNo P ≤ w → w < wNe P → σ₁ w = some (pNo P))) ∧
      (cpLow P ≤ P.cp → ∀ w : ℝ, wNe P ≤ w → σ₁ w = some (pNe P)) ∧
      (∀ w : ℝ, tier1Outcome σ₂ (σ₁ w) ≠ none ↔ min (wNe P) (wNo P) ≤ w) := by sorry

end FoodTrace.Adoption
