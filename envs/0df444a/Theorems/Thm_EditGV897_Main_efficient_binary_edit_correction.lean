-- Prove2me | Theorems.Thm_EditGV897_Main_efficient_binary_edit_correction
-- name    : EditGV897.Main.efficient_binary_edit_correction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:27:49.378089+00:00
-- url     : https://prove2.me/theorems/5a33700b-885c-499c-92c3-c72cde2a1dc4
-- title:
--   Theorem 1 — Efficient binary edit correction at GV redundancy
-- statement:
--   For every fixed integer $t\ge1$, there exist fixed deterministic setup, encoder and decoder programs, positive constants $C_t,A_t^{\mathrm{time}}$, a natural degree $d_t$, and a threshold $N_t\ge1$, all chosen before the block length and all inputs. For every $n\ge N_t$, setup constructs compact shared rows $H$ and a syndrome $\beta$. Let $F_{t,n}$ be the defined family of all length-preserving positioned scripts of at most $2t$ edits, $M=|F_{t,n}|$, $b=\lceil\log_2(2M)\rceil$, and $K=n-b-1$.
--
--   The family covers every distinct confusable pair. Setup returns $b<n$ independent rows, at most $2^{n-1}$ total surviving witnesses, and a syndrome with root certificate at least $2^K$. The encoder maps all $K$-bit messages injectively into separated words in this one syndrome class. Its image $C_n$ satisfies
--
--   $$|C_n|=2^K,\qquad r(C_n)=n-\log_2|C_n|=b+1\le2t\log_2n+C_t.$$
--
--   The code corrects every mixture of at most $t$ single-bit insertions, deletions and substitutions in total. For every information message $u$ and every finite received word $y$ reachable from its codeword within that budget,
--
--   $$\operatorname{Dec}(y)=u.$$
--
--   Actual halting executions realize setup, encoding and decoding within $A_t^{\mathrm{time}}(n+1)^{d_t}$ transitions each. Setup cost is included once and its output has polynomial bit length. Decoding includes recovery of the original information message, without access to its codeword or edit script.
--
--   This is the full constructive GV-redundancy result, with constant additive overhead and variable received lengths.
--
--   **Formalization Note** The explicit admissible choice is $C_t=\log_2((2t+1)[8(t+1)]^{2t})+3$, derived in planning from the proof's script bound; the paper prints no numerical additive constant or runtime degree. Only valid corrupted transmissions require decoder correctness and the stated $n$-only cost bound.
--
--   Differences from the source:
--   - encoding: ordered binary words and one-based positions → Fin n → ZMod 2, ordered lists, and zero-based positions; reason: these are order-preserving representations of the same words and legal edits
--   - encoding: an indexed family of affine edit maps → a list with occurrence multiplicity and membership in the canonical legal-script family; reason: equal induced maps remain separately indexed and fixed-point witnesses are excluded
--   - encoding: deterministic polynomial-time algorithms → fixed finite binary tape programs with actual halting executions bounded by positive uniform A(s+1)^d; reason: the fixed-tape bit model preserves polynomial time and charges input, output and all arithmetic work
--   - encoding: M=O_t(n^{2t}) and redundancy 2t log₂ n+O_t(1) → all legal scripts, M≤(2t+1)[8(t+1)]^{2t} n^{2t}, and C_t=log₂((2t+1)[8(t+1)]^{2t})+3; reason: this is the planning-derived admissible instantiation of the proof bound, not a claimed printed numerical constant
--   - encoding: one shared code and sufficiently large block lengths → the defined compact setup, its encoder image of exactly 2^K messages, and a uniform threshold N_t; reason: these expand the source construction without replacing its rate, edit model or message-recovery conclusion
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Theorem 1, §2.2, printed p. 5 / PDF p. 6; proof printed pp. 13–14 / PDF pp. 14–15

import Definitions.Def_EditGV897_Main_Codec

namespace EditGV897.Main

/-- Theorem 1 in full, with the source's concrete construction and a planning-derived
admissible additive constant. Programs and bounds are fixed before n and inputs. -/
theorem efficient_binary_edit_correction (t : ℕ) (ht : 1 ≤ t) :
    ∃ (constructor encoder decoder : Program) (C : ℝ) (A d N : ℕ),
      0 < C ∧ C = redundancyConstant t ∧ 0 < A ∧ 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        let K := messageLength P
        let code := codeImage F P
        EditFamily t F ∧ F.length ≤ familyCoefficient t * n ^ (2 * t) ∧
        P.rows.length = checkRows F.length ∧ P.rows.length < n ∧ FullRowRank P.rows ∧
        P.beta.length = P.rows.length ∧
        witnessSum F P.rows Finset.univ ≤ F.length * 2 ^ (n - P.rows.length) ∧
        witnessSum F P.rows Finset.univ ≤ 2 ^ (n - 1) ∧
        (2 ^ K : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) ∧
        (parametersCode P).length ≤ polyBudget A d n ∧
        Runs constructor (unary n) (parametersCode P) (polyBudget A d n) ∧
        Function.Injective (encodeWord F P) ∧ code.card = 2 ^ K ∧
        (n : ℝ) - logTwo code.card = (P.rows.length + 1 : ℕ) ∧
        (n : ℝ) - logTwo code.card ≤ (2 * t : ℕ) * logTwo n + C ∧
        DeletionHash.MixedEdit.Corrects 1 t code ∧
        (∀ u : Word K,
          let x := encodeWord F P u
          (encodeList F P u).length = n ∧ encodeList F P u = wordList x ∧
          syndrome P.rows x = P.beta ∧ Separated t P.rows x ∧
          inverseList F P (wordList x) = wordList u ∧
          Runs encoder (editEncoderInput P u) (wordCode x) (polyBudget A d n) ∧
          (∀ y : List Bit,
            DeletionHash.MixedEdit.Reaches 1 t (wordList x) y →
            decodeList t P y = some (wordList u) ∧
            Runs decoder (editDecoderInput P y) (wordCode u) (polyBudget A d n))) := by sorry

end EditGV897.Main
