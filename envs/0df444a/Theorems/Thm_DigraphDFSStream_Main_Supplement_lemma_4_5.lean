-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_lemma_4_5
-- name    : DigraphDFSStream.Main.Supplement.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:58:27.816286+00:00
-- url     : https://prove2.me/theorems/863dbe05-8ea3-4cdd-88de-c35af8d755a3
-- title:
--   Lemma 4.5 — path-count reduction
-- statement:
--   Let $G$ have $n\ge1$ vertices and let $\mathcal P$ be a multipath separator with $r$ paths. Put $L=\lceil\log_2 n\rceil+1$. Whenever $r>4(L+1)$, for every integer $1\le k\le n$ a uniform semi-streaming program returns a new multipath separator $\mathcal Q$ satisfying
--   $$|\mathcal Q|\le\lfloor r/2\rfloor,\qquad q=O((n/k+kp(n)+p(n))\log^2 n).$$
--   The separator threshold stays $n/2$. The bit budget and high-probability guarantee concern the same execution as the returned family. This is the path-count reduction used in constructing the small family of separator paths.
--
--   **Formalization Note** The integral floor expresses “at most $r/2$” exactly. The source leaves the leading resource constant unspecified; it is quantified before $n,k,p$ and the stream.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - encoding: L=ceil(log2 n)+1, r>4(L+1), at most r/2 paths → Nat.clog 2 n + 1, the identical strict threshold, and at most floor(r/2) paths; reason: path counts are integral, so floor(r/2) is exactly the printed half-count
--   - reading: the lemma uses the parameter k without stating its range; Section 4 introduces k in Proposition 4.1 as an integer with 1 <= k <= n → the statement holds for every integer k with 1 <= k <= n, k supplied in the charged header, one program for all k; reason: the lemmas are steps of Proposition 4.1's construction and inherit its k; n is the section's vertex count (the size bound in Lemma 4.3)
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.5, printed p.14 (PDF p.15)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Lemma 4.5, printed p.14 (PDF p.15). The fixed separator threshold is n/2.
The exact integral half-count is floor(r/2); L is ceil(log₂ n)+1. -/
theorem lemma_4_5 :
    ∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n →
            ∀ (input : List (Fin n × Fin n)) (paths : List (List (Fin n))),
              IsMultipathSeparator input.toFinset Finset.univ paths →
              4 * (L n + 1) < paths.length →
              Solves P input (natCode k ++ familyCode paths)
                (MultipathOutput input.toFinset (paths.length / 2))
                (workBits C d b n) (tradeoff C 2 true p n k) c n := by sorry

end DigraphDFSStream.Main.Supplement
