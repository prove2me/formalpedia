-- Prove2me | Theorems.Thm_ExactPatternStream_lemma_4_11
-- name    : ExactPatternStream.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:16.178984+00:00
-- url     : https://prove2.me/theorems/85ef8b72-7c12-4f68-b609-a27d85996c42
-- title:
--   Lemma 4.11 — the invariants of the hierarchy
-- statement:
--   For every $0\le i\le h$ and $S\in\{P,T\}$:
--
--   1. $\mathrm{leaves}(P_i[0])=\$\circ V_0'V_1'\cdots V_{i-1}'$;
--   2. $\mathrm{erase}(\overline S_i,\#)=S_0$;
--   3. if $|P_i|>1$, then $A^{(P)}_i[1]=1$;
--   4. every positive-index pattern node and every text node has a leaf string beginning with a character of $\Sigma$;
--   5. $|\mathrm{leaves}(R^{(S)}_i\circ\dots\circ R^{(S)}_0)|<w_i$.
--
--   The parse therefore loses nothing: the unrolled strings are the input with markers inserted, and the first pattern node absorbs the triggers so far.
--
--   Differences from the source:
--   - generalization: the standing assumptions $n\ge m\ge C$ of footnote 1 and $|\Sigma|\le n^{O(1)}$ of p.1 → every $m\ge1$ (with $m\le n\le2m$) and every alphabet size; reason: the proof uses no lower bound on $m$ and no bound on $|\Sigma|$ (only $n\le2m$ and $\mathcal L\ge8\lceil\log_2(m+1)\rceil$), and the source case is included
--   - encoding: $F_i$ of the form (6), "specified in Section 7.3" → an arbitrary argument `F`, with values $(y,z,\alpha)$; reason: §§4–5 of the source are written for any such $F_i$, and (14) is one
--   - encoding: $\Sigma$ an alphabet → characters are natural numbers; reason: every finite alphabet embeds
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.11, p.11 (PDF 12)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_Pad
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-- Gawrychowski, Janczewski, Jin, Nelson, *An Improved Streaming Algorithm for Exact Pattern Matching* (preprint, STOC 2027 submission, sha256 351218cb…), Lemma 4.11, p.11 (PDF 12).

The invariants of the hierarchy, for every choice of the hash functions `F_i`.

**Formalization Note.** `P T` satisfy the standing assumption `1 ≤ m ≤ n ≤ 2m` of p.3; the threshold `m ≥ C` of footnote 1 is not needed. (d) reads "every positive-index node of `P_i` and every node of `T_i`". `S̄_0` is `$ ◦ P` or `T`. -/
theorem lemma_4_11 (F : GroupHash) (P T : List ℕ) (hm : 1 ≤ P.length) (hmn : P.length ≤ T.length)
    (hn : T.length ≤ 2 * P.length) :
    let B := build F P T
    ∀ i ≤ topIndex B,
      let L := lvl B i
      L.P.head?.map ParseTree.leaves =
          some (Leaf.guard :: (List.range i).flatMap fun j => (lvl B j).V') ∧
        (erase L.Pbar Leaf.hash = (lvl B 0).Pbar ∧ erase L.Tbar Leaf.hash = (lvl B 0).Tbar) ∧
        (1 < L.P.length → L.AP.getD 1 false = true) ∧
        ((∀ t ∈ L.P.drop 1, ∃ a, t.leaves.head? = some (Leaf.sym a)) ∧
          ∀ t ∈ L.T, ∃ a, t.leaves.head? = some (Leaf.sym a)) ∧
        (leavesOf L.stackP).length < L.w ∧ (leavesOf L.stackT).length < L.w := by sorry

end ExactPatternStream
