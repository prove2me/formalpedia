-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_lemma_4_8
-- name    : DigraphDFSStream.Main.Supplement.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:00:46.118206+00:00
-- url     : https://prove2.me/theorems/949cb4bf-b22f-40c9-a183-a8d1b3e58ab0
-- title:
--   Lemma 4.8 — path-to-cycle conversion
-- statement:
--   Let $P$ be a nonempty simple directed path whose vertices form a separator of an $n$-vertex directed graph. A uniform semi-streaming program converts it to a directed cycle separator $Z$ with
--   $$q=O(p(n)\log n),\qquad\text{space}=\widetilde O(n).$$
--   The output lists the vertices in cyclic order. A singleton is permitted without a self-loop. It succeeds with high probability, and its bits and passes are bounded on every execution prefix. The fixed balance threshold is $n/2$.
--
--   This is the conversion needed after reducing a multipath separator to one path.
--
--   **Formalization Note** The nonempty path already implies nonempty input. The singleton case has exact correctness and fits the regularized logarithmic bounds.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.8, printed p.17 (PDF p.18)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Lemma 4.8, printed p.17 (PDF p.18). Singletons require no self-loop. -/
theorem lemma_4_8 :
    ∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ n : ℕ, 1 ≤ n →
            ∀ (input : List (Fin n × Fin n)) (path : List (Fin n)),
              SimplePath input.toFinset Finset.univ path →
              IsSeparator input.toFinset Finset.univ path.toFinset →
              Solves P input (vertexCode path) (CycleOutput input.toFinset)
                (workBits C d b n) (mergePasses C p n) c n := by sorry

end DigraphDFSStream.Main.Supplement
