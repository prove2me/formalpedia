-- Prove2me | Theorems.Thm_ContractionLemma_lemma_A_16_parameter_facts
-- name    : ContractionLemma.lemma_A_16_parameter_facts
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:57:14.624563+00:00
-- url     : https://prove2.me/theorems/3dd8002c-6e44-4c86-894f-cd65ab8a9eb1
-- title:
--   Lemma A.16 — parameter facts
-- statement:
--   For every $C>0$ there is a threshold $s^*$, depending only on $C$, such that for every $s\ge s^*$ and every call at depth $d$ with $H<M\le Cs8^{-d}$ edges:
--
--   1. (shallow) $2^d<C^{1/3}\lambda^{1/6}$;
--   2. (many levels) $u_d\ge\varepsilon\lambda/2^{d+1}\ge c_C\lambda^{5/6}$, where $c_C=\varepsilon/(2C^{1/3})$;
--   3. (small packets) $L\le s^{1/1000}$ and $Q\le s^{1/1000}$;
--   4. (size conditions) $M\ge 2Q^2\Delta$, $M\ge LQ$, $2L\le\Delta$, and $u_d\le a_d\le M$;
--   5. (enough nodes) $s^4>M(2L-1)+1$.
--
--   These facts show the recursion is shallow and every call satisfies the hypotheses of the packing lemma.
--
--   Differences from the source:
--   - generalization: every call at depth d with M > H → every edge count M with H < M ≤ C s 8^{−d}; reason: a reachable call has such an M, and this is the only fact about the call the proof uses
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Lemma A.16, p.75; proof pp.94–95

import Mathlib
import Definitions.Def_ContractionLemma_aSlot

set_option autoImplicit false

namespace ContractionLemma

/-- **Lemma A.16 (Parameter facts)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.75 (PDF p.78); proof pp.94–95.

There is a threshold `s*`, depending only on `C`, such that for every `s ≥ s*` and every call at
depth `d` with `H < M ≤ C s 8^{−d}` edges:
(a) (shallow) `2^d < C^{1/3} λ^{1/6}`;
(b) (many levels) `u_d ≥ ελ/2^{d+1} ≥ c_C λ^{5/6}`, where `c_C = ε/(2C^{1/3})`;
(c) (small packets) `L ≤ s^{1/1000}` and `Q ≤ s^{1/1000}`;
(d) (size conditions) `M ≥ 2Q²∆`, `M ≥ LQ`, `2L ≤ ∆` and `u_d ≤ a_d ≤ M`;
(e) (enough nodes) `s⁴ > M(2L − 1) + 1`.

**Formalization Note.** "Every call at depth `d`" is read as every edge count `M` in the range
`H < M ≤ C s 8^{−d}` that a call at depth `d` can have; `L = 2^{a_d}`, `Q = 64^{2a_d}`,
`∆ = ⌈s^{9/10}⌉`. -/
theorem lemma_A_16_parameter_facts (C : ℝ) (hC : 0 < C) :
    ∃ sStar : ℕ, ∀ s ≥ sStar, ∀ d M : ℕ, leafH s < M → (M : ℝ) ≤ C * s / 8 ^ d →
      (2 : ℝ) ^ d < C ^ ((1 : ℝ) / 3) * (lam s : ℝ) ^ ((1 : ℝ) / 6) ∧
      (epsC * lam s / 2 ^ (d + 1) ≤ (uLev s d : ℝ) ∧
        epsC / (2 * C ^ ((1 : ℝ) / 3)) * (lam s : ℝ) ^ ((5 : ℝ) / 6) ≤ epsC * lam s / 2 ^ (d + 1)) ∧
      ((2 : ℝ) ^ aSlot s d ≤ (s : ℝ) ^ ((1 : ℝ) / 1000) ∧
        (64 : ℝ) ^ (2 * aSlot s d) ≤ (s : ℝ) ^ ((1 : ℝ) / 1000)) ∧
      (2 * (64 ^ (2 * aSlot s d)) ^ 2 * degCap s ≤ M ∧ 2 ^ aSlot s d * 64 ^ (2 * aSlot s d) ≤ M ∧
        2 * 2 ^ aSlot s d ≤ degCap s ∧ uLev s d ≤ aSlot s d ∧ aSlot s d ≤ M) ∧
      M * (2 * 2 ^ aSlot s d - 1) + 1 < s ^ 4 := by sorry

end ContractionLemma
