-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_13
-- name    : APrioriTSP.Sampling.lemma_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:50.467799+00:00
-- url     : https://prove2.me/theorems/c15d1400-ee13-439e-8e2a-4a6512089048
-- title:
--   Lemma 13, p. 10 — the min-terms of (8) are bounded by b·ΣΣ e^{−(i+j−1)σbp}·min{B_i, B_j}
-- statement:
--   Let $\sigma \in (0,1)$, $0 < p < 1$, $b$ odd, and let $(C_j)_{j\ge1}$ satisfy $C_j \ge 0$ (6) and $C_{i+j} \le C_i + C_j$ for $i, j \ge 1$ (7). With the buckets $B_i$ of (9),
--   $$\sum_{k=1}^\infty (1-\sigma p)^{k-1}\sum_{i=1}^{k-1}\min\{C_i, C_{k-i}\} \;\le\; b\cdot\sum_{i=0}^\infty\sum_{j=0}^\infty e^{-(i+j-1)\sigma b p}\min\{B_i, B_j\} .$$
--
--   This bounds the connection-cost part of the sampling constraint (8) by a quantity that depends only on the buckets; with $\beta = bp$ it yields the bucket form (10) of (8).
--
--   **Formalization Note** The left side is written with the index shift $k \mapsto k+1$. Both sides are `tsum`s of nonnegative terms that converge under (6)–(7) ($C_k \le kC_1$, so $B_i$ grows at most linearly while the weights decay geometrically); the right side is an iterated sum over $i$, then $j$. The exponent $-(i+j-1)\sigma bp$ is real, so $i = j = 0$ gives $+\sigma bp$.
--
--   Differences from the source:
--
--   - generalization: C a feasible solution of (Sampling-OP), p = β/b (§2.2, p. 10) → any real sequence C satisfying (6) and (7), any p ∈ (0, 1); reason: the proof uses only (6) and (7); every p ∈ (0, 1) is β/b with β := bp, so the setting of §2.2 is an instance
--   - encoding: an odd integer b ≥ b_0 for the constant b_0 > 0 of §2 (p. 7) → every odd natural number b; reason: b_0 is an arbitrary positive constant, so every odd b ≥ 1 qualifies with b_0 := b
--   - generalization: σ = 0.663, fixed at the start of §2 (p. 7) → every σ ∈ (0, 1); reason: the argument uses only 0 < σ < 1, the range of Lemma 9 (ii); σ = 0.663 is an instance
--   - encoding: Σ_{k=1}^∞ (1 − σp)^{k−1} Σ_{i=1}^{k−1} min{C_i, C_{k−i}} → Σ_{k≥0} (1 − σp)^k Σ_{i=1}^{k} min{C_i, C_{k+1−i}} (index k ↦ k + 1), and the double series as iterated `tsum`s; reason: same series; all terms are nonnegative and both sides converge under (6)–(7)
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 10, Lemma 13 (proof p. 11)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Lemma 13 (p. 10): the min-terms of (8) are bounded through the buckets (left side shifted
`k ↦ k + 1`). -/
theorem lemma_13 (σ p : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (b : ℕ) (hb : Odd b) (C : ℕ → ℝ) (hC0 : ∀ i, 1 ≤ i → 0 ≤ C i)
    (hC : ∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) :
    ∑' k : ℕ, (1 - σ * p) ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤
      (b : ℝ) * ∑' i : ℕ, ∑' j : ℕ,
        Real.exp (-(((i : ℝ) + j - 1) * σ * b * p)) * min (bucket b C i) (bucket b C j) := by sorry

end APrioriTSP.Sampling
