-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_price_nonneg
-- name    : BauerleRiederMDP.Indifference.price_nonneg
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:21.388526+00:00
-- url     : https://prove2.me/theorems/ddc48a3b-2a15-49ad-8ae0-c413dfe30699
-- title:
--   §4.9, p.140 — $d_n\ge v^{N-n}>0$ and the indifference price is non-negative
-- statement:
--   For a claim $H\ge 0$ with maturity $N$, every $n\le N$ and all prices $s,\hat s\ge 0$,
--   $$
--   d_n(s,\hat s)\ge v^{N-n}>0,
--   $$
--   and consequently $v_n(H,s,\hat s)\ge 0$: the seller of a non-negative claim asks for a non-negative price.
--
--   Differences from the source:
--   - reading: the indifference price is positive, since d_n ≥ v^{N−n} > 0 → the indifference price is non-negative; reason: the printed inequality gives ≥ 0, and for H ≡ 0 the price is 0, so the word positive cannot be strict
--   - generalization: prices s > 0, ŝ > 0 → all s, ŝ ≥ 0, the whole price part of E = ℝ × ℝ₊²; reason: the book's prices are included
--   - reading: (FM) prints only d̂ < û → hypothesis 0 ≤ d̂; reason: the multiperiod model puts the relative price changes in 𝒵 := ℝ₊ × ℝ₊ (p.138), so the prices stay in ℝ₊ where the claim is non-negative
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.140, paragraph after the proof of Theorem 4.9.4

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_IsIndifferencePrice
import Definitions.Def_BauerleRiederMDP_Indifference_Market_v
import Definitions.Def_BauerleRiederMDP_Indifference_Market_dseq

namespace BauerleRiederMDP.Indifference

/-- `d_n(s, ŝ) ≥ v^{N-n} > 0`, and hence the indifference price is non-negative (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), §4.9, p.140, PDF 154).

**Formalization Note.** The book writes "positive" for what its inequality `d_n ≥ v^{N-n}` gives:
for `H ≡ 0` the price is `0`. `0 ≤ d̂` is the book's `𝒵 := ℝ₊ × ℝ₊` (p.138). -/
theorem price_nonneg (M : Market) (hdhat : 0 ≤ M.dhat) (N : ℕ) (H : Claim) (n : ℕ) (hn : n ≤ N)
    (s ŝ : ℝ) (hs : 0 ≤ s) (hŝ : 0 ≤ ŝ) :
    M.v ^ (N - n) ≤ M.dseq N H n s ŝ ∧ 0 < M.v ^ (N - n) ∧
      0 ≤ M.indifferencePrice N H n s ŝ := by sorry

end BauerleRiederMDP.Indifference
