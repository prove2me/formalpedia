-- Prove2me | Theorems.Thm_CellProbeTree_Matching_lemma_4_2
-- name    : CellProbeTree.Matching.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:35:51.059734+00:00
-- url     : https://prove2.me/theorems/567871cd-d1ab-4f06-b0b8-8d12d80a48ec
-- title:
--   Lemma 4.2 — physical query identities (31)–(33) for the LR block
-- statement:
--   In an LR block with $u \ge 1$, forests of total sizes $a, b$, $B = a + b + 2u$ and an interleaving word with $u$ letters of each kind (1-based positions), the openings created by the spine steps and their mates satisfy, for $1 \le i, j \le u$,
--   $$q^R_i = 2\alpha_{i-1} + 2i + k_L(i) - 1, \qquad \mathrm{findclose}(q^R_i) = 2\alpha_i + 2i + k_L(i), \tag{31}$$
--   $$q^L_j = 2\alpha_{k_R(j)} + 2k_R(j) + j, \qquad c_j := \mathrm{findclose}(q^L_j) = 2B - 2\beta_j - j + 1. \tag{32}$$
--   The $L$-openings are exactly the opening positions $q$ with
--   $$q < c_{\mathrm{piv}} + \tfrac12 < \mathrm{findclose}(q), \qquad c_{\mathrm{piv}} = 2a + 3u. \tag{33}$$
--   For the common query algorithm, an answer to the right of $q$ identifies $q$ as an opening: if the mate of $q$ lies to the right of $q$, position $q$ holds `(`.
--
--   Differences from the source:
--   - encoding: "the opening created by the spine step $R_i$ (resp. $L_j$)" → the unique position whose tag in `blockTagged` is `some (true, i)` (resp. `some (false, j)`), stated as: a position $q \ge 1$ carries that tag iff $q$ equals the formula; reason: the tags record which step created each opening.
--   - encoding: $\mathrm{findclose}(q) = c$ → `IsOpenMate W q c`; $c_j$ given as an integer equal to $2B - 2\beta_j - j + 1$; reason: matching is a relation; integer arithmetic avoids truncated subtraction.
--   - reading: "$q < c_{\mathrm{piv}} + 1/2 < \mathrm{findclose}(q)$" → $q \le c_{\mathrm{piv}} < \mathrm{findclose}(q)$; reason: equivalent for integer positions.
--   - reading: "Thus a completed query certifies membership in this set without supplying its hidden spine rank" → not a separate clause; reason: it is a remark that follows from (33) and the preceding sentence, both of which are stated.
-- source:
--   Liang, Liu, Nearly Tight Cell-Probe Lower Bounds for Querying on Tree via Talagrand Inequality, STOC 2027 submission (manuscript sha256 0e5a8eb2…), pp. 18–19, Lemma 4.2, equations (31)–(33)

import Mathlib
import Definitions.Def_CellProbeTree_Matching_Mate
import Definitions.Def_CellProbeTree_Matching_LRBlock

namespace CellProbeTree.Matching

/-- Lemma 4.2 (physical query identities), 1-based positions in the block word `W`:
the opening of step `R_i` is at `q^R_i = 2α_{i−1} + 2i + k_L(i) − 1` with
`findclose(q^R_i) = 2α_i + 2i + k_L(i)` (31); the opening of step `L_j` is at
`q^L_j = 2α_{k_R(j)} + 2k_R(j) + j` with `findclose(q^L_j) = 2B − 2β_j − j + 1` (32); the
`L`-openings are exactly the openings `q` with `q < c_piv + 1/2 < findclose(q)` (33); and an answer
to the right of `q` identifies `q` as an opening. -/
theorem lemma_4_2 (u a b Bsz : ℕ) (hu : 1 ≤ u) (hB : Bsz = a + b + 2 * u)
    (A B : Fin u → BinaryTree Unit) (σ : Fin (2 * u) → Bool)
    (hA : forestSize A = a) (hBf : forestSize B = b) (hσ : σ ∈ sigmaWords u) :
    let T := blockTagged u A B σ
    let W := blockWord u A B σ
    let kL : ℕ → ℕ := precCount (List.ofFn σ) true
    let kR : ℕ → ℕ := precCount (List.ofFn σ) false
    -- (31)
    (∀ i : ℕ, 1 ≤ i → i ≤ u →
      (∀ q : ℕ, 1 ≤ q →
        ((T[q - 1]?).map Prod.snd = some (some (true, i)) ↔
          q = 2 * prefixSize A (i - 1) + 2 * i + kL i - 1)) ∧
      IsOpenMate W (2 * prefixSize A (i - 1) + 2 * i + kL i - 1)
        (2 * prefixSize A i + 2 * i + kL i)) ∧
    -- (32)
    (∀ j : ℕ, 1 ≤ j → j ≤ u →
      (∀ q : ℕ, 1 ≤ q →
        ((T[q - 1]?).map Prod.snd = some (some (false, j)) ↔
          q = 2 * prefixSize A (kR j) + 2 * kR j + j)) ∧
      ∃ c : ℕ, (c : ℤ) = 2 * (Bsz : ℤ) - 2 * (prefixSize B j : ℤ) - (j : ℤ) + 1 ∧
        IsOpenMate W (2 * prefixSize A (kR j) + 2 * kR j + j) c) ∧
    -- (33)
    (∀ q : ℕ,
      (∃ j : ℕ, 1 ≤ j ∧ j ≤ u ∧ (T[q - 1]?).map Prod.snd = some (some (false, j)) ∧ 1 ≤ q) ↔
        ∃ c : ℕ, IsOpenMate W q c ∧ q ≤ 2 * a + 3 * u ∧ 2 * a + 3 * u < c) ∧
    -- an answer to the right identifies an opening
    (∀ q c : ℕ, 1 ≤ q → 1 ≤ c → Mate W (q - 1) (c - 1) → q < c → W[q - 1]? = some DyckStep.U) := by sorry

end CellProbeTree.Matching
