-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_lemma_4_6
-- name    : DigraphDFSStream.Main.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:59:20.430539+00:00
-- url     : https://prove2.me/theorems/5f2ae7b4-382c-4278-9b85-3066cd87d5a5
-- title:
--   Lemma 4.6 — few-path separator
-- statement:
--   For every directed graph on $n\ge1$ vertices and every integer $1\le k\le n$, a uniform semi-streaming program returns, with high probability, a multipath separator $\mathcal P$ with
--   $$|\mathcal P|\le4(L+1),\quad L=\lceil\log_2 n\rceil+1,\qquad q=O((n/k+kp(n)+p(n))\log^3 n).$$
--   This family retains the graph's fixed $n/2$ balance threshold. The path-count bound is the explicit stopping threshold in the source proof, hence implies the printed $O(\log n)$ conclusion. Memory is bounded on every execution prefix, including unsuccessful tapes.
--
--   **Formalization Note** No numerical leading constant is supplied by the source for passes or bits. The uniform constants and the local memory exponent remain existential, before the primitive budgets and graph inputs.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - encoding: O(log n) paths; proof stops at at most 4(L+1) → at most 4*(L(n)+1) paths; reason: this is the exact explicit stopping bound in the source proof, not an invented O-constant
--   - reading: the lemma uses the parameter k without stating its range; Section 4 introduces k in Proposition 4.1 as an integer with 1 <= k <= n → the statement holds for every integer k with 1 <= k <= n, k supplied in the charged header, one program for all k; reason: the lemmas are steps of Proposition 4.1's construction and inherit its k; n is the section's vertex count (the size bound in Lemma 4.3)
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.6, printed p.16 (PDF p.17)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Lemma 4.6, printed p.16 (PDF p.17). The proof gives the explicit 4(L+1) path bound. -/
theorem lemma_4_6 :
    ∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n →
            ∀ input : List (Fin n × Fin n),
              Solves P input (natCode k) (MultipathOutput input.toFinset (4 * (L n + 1)))
                (workBits C d b n) (tradeoff C 3 true p n k) c n := by sorry

end DigraphDFSStream.Main.Supplement
