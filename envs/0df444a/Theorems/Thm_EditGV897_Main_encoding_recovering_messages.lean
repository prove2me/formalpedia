-- Prove2me | Theorems.Thm_EditGV897_Main_encoding_recovering_messages
-- name    : EditGV897.Main.encoding_recovering_messages
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:28:16.908343+00:00
-- url     : https://prove2.me/theorems/4887cd2c-e1fd-4497-a566-0ee47b988196
-- title:
--   Lemma 3 — Encoding and recovering messages
-- statement:
--   Let $t\ge1$, let $F$ be an admissible indexed affine edit family of size $M\ge1$, and fix shared rows $G$ and syndrome $\beta$. Put $b=|G|=\lceil\log_2(2M)\rceil<n$ and $K=n-b-1$. Assume full row rank, $|\beta|=b$, and the Part 2 root certificate $L_G(D_{G,\beta})\ge2^K$.
--
--   The specified signed-bound construction encodes every $K$-bit message $u$ injectively as a separated length-$n$ word $x$ with syndrome $\beta$, and its specified image inverse recovers the original message:
--
--   $$\operatorname{Inv}(\operatorname{Enc}(u))=u,\qquad G\operatorname{Enc}(u)=\beta.$$
--
--   The final residual index is zero. Fixed deterministic encoder and inverter programs realize these outputs in at most $A(n+M+1)^d$ transitions, with $A>0$ and natural $d$ uniform before all inputs. Encoding covers all $2^K$ messages, including the empty message at $K=0$.
--
--   This indexes the guaranteed code subset and provides the original-message recovery required by Theorem 1.
--
--   **Formalization Note** Only the root lower bound is assumed positive. Other prefix bounds may be negative; only the one-branch subtraction uses a maximum with zero. Inversion is guaranteed on the encoder image.
--
--   Differences from the source:
--   - encoding: ordered binary words and one-based positions → Fin n → ZMod 2, ordered lists, and zero-based positions; reason: these are order-preserving representations of the same words and legal edits
--   - encoding: an indexed family of affine edit maps → a list with occurrence multiplicity and membership in the canonical legal-script family; reason: equal induced maps remain separately indexed and fixed-point witnesses are excluded
--   - encoding: deterministic polynomial-time algorithms → fixed finite binary tape programs with actual halting executions bounded by positive uniform A(s+1)^d; reason: the fixed-tape bit model preserves polynomial time and charges input, output and all arithmetic work
--   - encoding: signed lower bounds and nonnegative running indices → integer lower bounds and integer traversal indices with max(0,L(p0)) only in branch subtraction; reason: this preserves negative unused-child bounds and the exact source branch rule
--   - generalization: the particular full-rank rows and syndrome obtained in Part 2 → any full-rank rows and syndrome with the same prescribed row count and root certificate; reason: Part 2 supplies these conditions and the source proof of Lemma 3 uses only these conditions
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, Lemma 3, §4.3, printed p. 12 / PDF p. 13, proof continuing printed p. 13 / PDF p. 14

import Definitions.Def_EditGV897_Main_Codec

namespace EditGV897.Main

/-- Lemma 3. Only the root signed bound is positive by hypothesis; other
prefix bounds may be negative. Inversion is asserted on the encoder image. -/
theorem encoding_recovering_messages :
    ∃ (encoder inverter : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (P : Parameters n),
        1 ≤ t → EditFamily t F → P.rows.length = checkRows F.length → P.rows.length < n →
        FullRowRank P.rows → P.beta.length = P.rows.length →
        (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) →
        Function.Injective (encodeWord F P) ∧
        (∀ u : Word (messageLength P),
          let x := encodeWord F P u
          encodeList F P u = wordList x ∧ (encodeList F P u).length = n ∧
          syndrome P.rows x = P.beta ∧ Separated t P.rows x ∧
          (encodeSteps F P n [] (messageIndex (wordList u))).2 = 0 ∧
          inverseList F P (wordList x) = wordList u ∧
          Runs encoder (encoderInput F P u) (wordCode x) (polyBudget A d (n + F.length)) ∧
          Runs inverter (inverseInput F P (wordList x)) (wordCode u)
            (polyBudget A d (n + F.length))) := by sorry

end EditGV897.Main
