-- Prove2me | Theorems.Thm_BwSC_LowerBound_lemma_13
-- name    : BwSC.LowerBound.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:22.477887+00:00
-- url     : https://prove2.me/theorems/26ffd9cc-e820-4e9b-852f-5c0ef83eb900
-- title:
--   Lemma 13, p. 74 — Σ_{j∈[q+2]} Σ_k D_re(P″_{j,k}‖Q″_{j,k}) ≤ K/(8(q+2)); average ≤ 1/(8(q+2)²) ≤ q̄^(2)/4 (stopped records)
-- statement:
--   Let $K>1$, $T\ge2K$, $\pi\in\Pi_S$, $q=q(S,K)$. With the reverse KL divergence and the second-class artificial measures $\mathbb P''_{j,k},\mathbb Q''_{j,k}$ (stopped at the first pull of arm $k$ in the window $[t^{(2)}_{j-1}:t^{(2)}_j]$),
--   $$\sum_{j\in[q+2]}\sum_{k\in[K]}D_{\rm re}\big(\mathbb P''_{j,k}\,\|\,\mathbb Q''_{j,k}\big)\ \le\ \frac{K}{8(q+2)},$$
--   and, combined with Corollary 4 under $\mathbb Q$,
--   $$\frac1{(q+2)K}\sum_{j\in[q+2]}\sum_{k\in[K]}D_{\rm re}\big(\mathbb P''_{j,k}\,\|\,\mathbb Q''_{j,k}\big)\ \le\ \frac{1}{8(q+2)^2}\ \le\ \frac{\overline{q^{(2)}}}{4}.$$
--
--   This is the divergence bound fed into the reverse Fano inequality in (47).
--
--   **Formalization Note** The page's first display writes $\mathbb Q'_{j,k}$, a typo for $\mathbb Q''_{j,k}$, and its definition of $\mathbb P''_{j,k}$ (p. 73) writes $\mu^{(1)}_{j,k}$ in the first block, a typo for $\mu^{(2)}_{j,k}$. The measures are the stopped repair described in Lemma 12 and in `BwSC.LowerBound.Proof`.
-- source:
--   Simchi-Levi & Xu, Phase Transitions in Bandits with Switching Constraints, arXiv:1905.10825v4, p. 74, Lemma 13; artificial measures pp. 73–74

import Mathlib
import Definitions.Def_BwSC_LowerBound_Proof

open MeasureTheory ProbabilityTheory InformationTheory BanditAlgorithm
open scoped ENNReal

namespace BwSC.LowerBound

/-- Lemma 13, p. 74 (for the artificial measures stopped at the first pull of arm `k` in the
window): `Σ_{j ∈ [q+2]} Σ_{k ∈ [K]} D_re(P''_{j,k} ∥ Q''_{j,k}) ≤ K/(8(q(S,K)+2))`; combined with
Corollary 4, the average is at most `1/(8(q+2)²) ≤ q̄^{(2)}/4`. -/
theorem lemma_13 {K S T : ℕ} (hK : 1 < K) (hT : 2 * K ≤ T) (π : BanditPolicy K)
    (hπ : IsSwitchPolicy S T π) :
    ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K, klDiv (artQ2 π S T j k) (artP2 π S T j k) ≤
        ENNReal.ofReal ((K : ℝ) / (8 * ((qIdx S K : ℝ) + 2))) ∧
    ENNReal.ofReal (1 / (((qIdx S K : ℝ) + 2) * K)) *
        ∑ j ∈ Finset.Icc 1 (qIdx S K + 2), ∑ k : Fin K,
          klDiv (artQ2 π S T j k) (artP2 π S T j k) ≤
        ENNReal.ofReal (1 / (8 * ((qIdx S K : ℝ) + 2) ^ 2)) ∧
    1 / (8 * ((qIdx S K : ℝ) + 2) ^ 2) ≤ qbar2 π S T / 4 := by sorry

end BwSC.LowerBound
