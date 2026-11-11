-- Prove2me | Theorems.Thm_CatalanHashing_Dynamic_theorem_1_4
-- name    : CatalanHashing.Dynamic.theorem_1_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:06:15.291921+00:00
-- url     : https://prove2.me/theorems/0f3cae37-cac8-4c91-9cdd-188bc16435b2
-- title:
--   Theorem 1.4 — dynamic high-load Catalan hashing: load 1 − ε with amortized expected scan cost O(|x|/ε) per positive query, O(1/ε) per negative query and O(|x| log^{1+δ}|x|/ε) per update
-- statement:
--   For every $\delta>0$ there are constants $C=C(\delta)$, $c_w$, $b$ and $c_g$ such that for every number of cells $N\ge1$, every $\varepsilon\in(0,\tfrac12)$ and every word size $w\ge c_w\log_2N$ there is a dynamic dictionary on $N$ cells, each holding one $w$-bit word and $b$ metadata bits, keeping at most $c_g(\lceil\log_2N\rceil+1)^2$ words of global state, with the following property. For every operation sequence $\sigma$ fixed in advance that is valid for $(N,\varepsilon)$ (insertions of absent keys, deletions of present keys, queries of any key, live volume at most $(1-\varepsilon)N$ after every operation):
--
--   - the total scan cost is measurable and, almost surely, every query of $\sigma$ is answered correctly;
--   - the expected total scan cost obeys
--   $$\mathbb E\Big[\sum_{\mathrm{op}\in\sigma}\mathrm{cost}(\mathrm{op})\Big]\;\le\;C\sum_{\mathrm{op}\in\sigma}b(\mathrm{op}),$$
--   with $b(\mathrm{op})=|x|/\varepsilon$ for a positive query for $x$, $1/\varepsilon$ for a negative query (whatever the key length), and $|x|(\log|x|)^{1+\delta}/\varepsilon$ for an insertion or deletion of $x$, where $\log s=\max\{1,\log_2s\}$.
--
--   This is the paper's main result: a linear-probing-like table for variable-length items at load factor $1-\varepsilon$ whose queries scan $O(|x|/\varepsilon)$ cells, matching the fixed-size case up to constants.
--
--   **Formalization Note.** The model is the definition `CatalanHashing.Dynamic.Model`: programs are decision trees that read and write cells and evaluate fully random hash functions; only the $N$ cells and the global state persist between operations. Correctness is required because a table that touches nothing and always answers Not Found would otherwise have scan cost 0.
--
--   Differences from the source:
--
--   - reading: "a dynamic Catalan hash table operating at load factor 1 − ε" with "O(1) bits of metadata per cell" (Theorems 1.1, 1.3) and metadata not counted in the load (p. 7) → N cells of one w-bit word and b metadata bits (b a constant chosen with C), at most c_g(⌈log₂ N⌉+1)² words of persistent global state, load measured against all N cells; reason: reading R1: the strongest reading the construction meets (its O(1)-word auxiliary metadata lives in the Θ(εN) auxiliary cells; Section 8 keeps O(log² m) bookkeeping words); unbounded metadata or global state would trivialise the theorem
--   - reading: word-RAM operations with transient working memory; the cache-oblivious I/O model → each operation is a finite adaptive decision tree (read and branch, write, evaluate a hash and branch, halt with an answer and the new global state); transient memory is unbounded within an operation; reason: scan cost only counts accessed cells, so only reads and writes of the array matter; the I/O corollary is not part of Theorem 1.4
--   - encoding: fully random h onto [0, m), further independent hash functions (fingerprints φ, ψ, the random rotation) → countably many independent uniform [0, 1]-valued functions ω (j, ·) of the key; reason: rescaling; [0, 1] and [0, 1) differ by a null set
--   - reading: "the sequence of operations is fixed in advance" (oblivious adversary); inserting absent keys and deleting present keys (§8.2) → ∀ σ : List (Op w), Valid N ε σ, quantified after the dictionary D and before ω; Valid requires absent-key insertions, present-key deletions and live volume ≤ (1 − ε)N after every operation; reason: the construction may depend on (N, ε, w, δ) but not on σ; load factor 1 − ε holds at every moment
--   - reading: item x = (k, v) stored as |x| ≥ 1 words, encoded so the key can be read off a prefix → |x| = |k| + |v| with k a nonempty word list and v a word list; reason: any self-delimiting encoding changes |x| by at most a factor 2, absorbed in the O(·)
--   - reading: log^{1+δ}|x| with "log s = max{1, log₂ s}" (p. 7) → logC s = max 1 (Real.logb 2 s), raised to the real power 1 + δ; reason: the paper's stated convention for asymptotic bounds
--   - reading: "amortized expected scan cost" O(|x|/ε), O(1/ε), O(|x| log^{1+δ}|x|/ε) → E[Σ_{op ∈ σ} cost(op)] ≤ C Σ_{op ∈ σ} b(op) for every valid σ, with one C depending only on δ, and b(negative query) = 1/ε whatever the key length (p. 7); reason: this is the accounting of Proposition 8.4's proof; it holds for every prefix since prefixes of valid sequences are valid
--   - reading: "supports positive queries ... and negative queries" → ∀ᵐ ω, every query returns the live value of its key or Not Found accordingly; and the total cost is measurable; reason: supporting a query includes answering it; almost surely because hash ties (probability 0) are not handled (footnote 3); measurability makes the expectation the real one
--   - reading: "a word has at least c_w log m bits for some constant c_w" (p. 7) → ∃ cw : ℕ before N, and the guarantee for every w with cw · log₂ N ≤ w; reason: c_w is a constant of the construction; a natural-number constant is no loss (round up)
-- source:
--   Conway, Komlós, Kuszmaul, Catalan Hashing: Efficient Linear Probing for Variable-Length Items, arXiv:2611.05235 (copy sha256 e2048176…), p. 5, Theorem 1.4 (PDF 6); restated as Proposition 8.4, p. 34 (PDF 35)

import Mathlib
import Definitions.Def_CatalanHashing_Dynamic_Model

open MeasureTheory
open scoped ENNReal

namespace CatalanHashing.Dynamic

/-- Theorem 1.4 (dynamic high-load Catalan hashing). For every `δ > 0` there are constants
`C`, `c_w`, `b`, `c_g` such that for every `N ≥ 1`, `ε ∈ (0, 1/2)` and word size
`w ≥ c_w log₂ N` some dictionary on `N` cells of one word and `b` metadata bits, with at most
`c_g (⌈log₂ N⌉ + 1)²` words of global state, answers every query of every valid oblivious
operation sequence correctly almost surely, and has expected total scan cost at most
`C Σ_op b(op)`. -/
theorem theorem_1_4 :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∃ cw b cg : ℕ,
      ∀ N : ℕ, 1 ≤ N → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ w : ℕ, (cw : ℝ) * Real.logb 2 N ≤ w →
        ∃ D : Dictionary N w b, D.GlobalBounded (globalAllowance N cg) ∧
          ∀ σ : List (Op w), Valid N ε σ →
            Measurable (fun ω => (D.totalCost σ ω : ℝ≥0∞)) ∧
            (∀ᵐ ω ∂(omegaMeasure w), D.Correct σ ω) ∧
            ∫⁻ ω, (D.totalCost σ ω : ℝ≥0∞) ∂(omegaMeasure w) ≤
              ENNReal.ofReal (C * totalBudget ε δ σ) := by sorry

end CatalanHashing.Dynamic
