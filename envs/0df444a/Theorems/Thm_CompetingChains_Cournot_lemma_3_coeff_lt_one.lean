-- Prove2me | Theorems.Thm_CompetingChains_Cournot_lemma_3_coeff_lt_one
-- name    : CompetingChains.Cournot.lemma_3_coeff_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:38.765096+00:00
-- url     : https://prove2.me/theorems/7e3ea155-6eef-4fd6-a660-76868d19aa2e
-- title:
--   Proof of Lemma 3, p. 28 — every response coefficient satisfies C^{X_jX_i}_j < 1
-- statement:
--   Let $k>1/3$, $0\le\gamma_C<1$, $t>0$ and $\sigma^2>0$, and let $C^{X_iX_j}$ be the Cournot response coefficients of Lemma 2(a). Then for all arrangements $X_i,X_j\in\{S,N\}$,
--
--   $$
--   C^{X_iX_j}<1 .
--   $$
--
--   In the paper this gives the sign of the wholesale price and cost-reduction coefficients (Lemma 3(a)); in this mission it guarantees $1-\gamma_C C_j>0$, which the comparisons of profits use.
-- source:
--   Ha, Tian & Tong, Information Sharing in Competing Supply Chains with Production Cost Reduction (MSOM 2017, pre-published version), p. 28, proof of Lemma 3, first sentence

import Mathlib
import Definitions.Def_CompetingChains_Cournot_Setting

namespace CompetingChains.Cournot

theorem lemma_3_coeff_lt_one (k γ t σsq : ℝ) (hk : 1 / 3 < k) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (ht : 0 < t) (hσ : 0 < σsq) :
    ∀ Xi Xj : Arrangement, C k γ t σsq Xi Xj < 1 := by sorry

end CompetingChains.Cournot
