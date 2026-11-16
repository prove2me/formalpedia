-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_lemma_4_7
-- name    : DigraphDFSStream.Main.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:59:51.157026+00:00
-- url     : https://prove2.me/theorems/75a6870c-24b1-4d20-a58e-9a05162d9d8b
-- title:
--   Lemma 4.7 — merge two paths, fixing the others
-- statement:
--   Let $P_1,P_2$ be two selected paths in a multipath separator of an $n$-vertex directed graph. Let $\mathcal R$ be its list of all other paths. A uniform semi-streaming program returns a family $\mathcal Q$ satisfying
--   $$|\mathcal Q|\le1,\qquad\mathcal Q\mathbin{+\!+}\mathcal R\text{ is a multipath separator},\qquad q=O(p(n)\log n).$$
--   The entire list $\mathcal R$ is kept unchanged, and the output encodes the resulting full family. The resource bound is on every tape and correctness is with high probability. The separator balance threshold remains $n/2$.
--
--   **Formalization Note** The output may contain no replacement path when the unselected paths already form a separator. Retaining their list order is a representation convention; no vertex or edge of an unselected path changes.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - encoding: two paths replaced by at most one, keeping all other paths fixed → the output family is Q ++ others with length(Q)<=1; reason: listing the selected paths first is an input convention; every original family and choice of two paths is represented
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.7, printed p.16 (PDF p.17)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Lemma 4.7, printed p.16 (PDF p.17). The unselected paths are retained literally. -/
theorem lemma_4_7 :
    ∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ n : ℕ, 1 ≤ n →
            ∀ (input : List (Fin n × Fin n)) (first second : List (Fin n))
              (others : List (List (Fin n))),
              IsMultipathSeparator input.toFinset Finset.univ (first :: second :: others) →
              Solves P input (familyCode (first :: second :: others))
                (MergeOutput input.toFinset others)
                (workBits C d b n) (mergePasses C p n) c n := by sorry

end DigraphDFSStream.Main.Supplement
