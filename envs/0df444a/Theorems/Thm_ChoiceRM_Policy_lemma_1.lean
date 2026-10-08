-- Prove2me | Theorems.Thm_ChoiceRM_Policy_lemma_1
-- name    : ChoiceRM.Policy.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:04.012059+00:00
-- url     : https://prove2.me/theorems/ea2a0a24-f9fc-42d2-a5e2-715973120535
-- title:
--   Lemma 1, p. 12 — higher-indexed winner persists at lower values
-- statement:
--   Take two nondominated sets indexed $k<l$ in nondecreasing purchase-probability order. If $v_0\ge0$ and set $l$ strictly beats set $k$ at $v_0$, then it strictly beats it at every $v\le v_0$:
--
--   $$R_l-Q_lv_0>R_k-Q_kv_0\quad\Longrightarrow\quad R_l-Q_lv>R_k-Q_kv\quad(v\le v_0).$$
--
--   This comparison is the order step used to control changes in the optimal index.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 12, Lemma 1

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance

namespace ChoiceRM.Policy

open RevenueManagement

/-- Lemma 1 (p. 12): a higher indexed set that wins at `v₀` wins at every lower `v`. -/
theorem lemma_1 {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k)))
    (k l : Fin m) (hkl : k < l) (v₀ : ℝ) (hv₀ : 0 ≤ v₀)
    (h : expRevenue P r (Sq k) - purchaseProb P (Sq k) * v₀ <
      expRevenue P r (Sq l) - purchaseProb P (Sq l) * v₀) :
    ∀ v : ℝ, v ≤ v₀ →
      expRevenue P r (Sq k) - purchaseProb P (Sq k) * v <
        expRevenue P r (Sq l) - purchaseProb P (Sq l) * v := by sorry

end ChoiceRM.Policy
