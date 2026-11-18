-- Prove2me | Theorems.Thm_EditGV897_Main_encoding_programs
-- name    : EditGV897.Main.encoding_programs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:49:20.469309+00:00
-- url     : https://prove2.me/theorems/9ddd2ab6-cbc5-4dc7-af91-5e1d6949d306
-- title:
--   Polynomial-time tape realizations of encoding and image inversion
-- statement:
--   There are fixed finite binary tape programs for encoding and image inversion, and uniform natural constants $A>0$ and $d$, with the following guarantee. Let $n$ be the block length, $t\ge1$, and $F$ a family of $M$ affine edit maps. Let $P=(H,\beta)$ satisfy the shared-parameter conditions of Lemma 3: $H$ has full row rank, has $b=\lceil\log_2(2M)\rceil<n$ rows, $\beta$ has $b$ bits, and the root signed bound is at least $2^K$, where $K=n-b-1$.
--
--   For every $K$-bit message $u$, actual halting tape executions compute its specified signed-bound codeword and recover $u$ from that codeword, each in at most
--
--   $$A(n+M+1)^d$$
--
--   transitions. Inputs include the dimension, dense affine family, parity rows, syndrome, and framed message or codeword. This is the computational part of Lemma 3. The finite-program operational model charges parsing, arithmetic, counting, and output writing.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §4.3, Lemma 3 and its proof, printed pp.12–13 / PDF pp.13–14

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.encoding_programs :
    ∃ (encoder inverter : Program) (A d : ℕ), 0 < A ∧
      ∀ (n t : ℕ) (F : Family n) (P : Parameters n),
        1 ≤ t → EditFamily t F → P.rows.length = checkRows F.length → P.rows.length < n →
        FullRowRank P.rows → P.beta.length = P.rows.length →
        (2 ^ messageLength P : ℤ) ≤ signedBound F P.rows (coset P.rows P.beta) →
        ∀ u : Word (messageLength P),
          Runs encoder (encoderInput F P u) (wordCode (encodeWord F P u))
            (polyBudget A d (n + F.length)) ∧
          Runs inverter (inverseInput F P (wordList (encodeWord F P u))) (wordCode u)
            (polyBudget A d (n + F.length)) := by sorry
