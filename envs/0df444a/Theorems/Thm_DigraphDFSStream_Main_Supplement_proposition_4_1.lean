-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_proposition_4_1
-- name    : DigraphDFSStream.Main.Supplement.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:01:35.021059+00:00
-- url     : https://prove2.me/theorems/04402190-7288-4710-8185-7790e2f5f224
-- title:
--   Proposition 4.1 — cycle-separator tradeoff and specialization
-- statement:
--   For an $n$-vertex directed graph with $n\ge1$, and every integer $1\le k\le n$, there is a uniform semi-streaming program returning a directed cycle separator in cyclic vertex order, with high probability, using
--   $$q=O((n/k+kp(n))\log^3 n)\quad\text{passes and}\quad\widetilde O(n)\text{ bits}.$$
--   A singleton requires no self-loop. The statement also retains the specialization obtained with the currently available $p(n)=n^{1/2+o(1)}$ primitives:
--   $$k=\lceil n^{1/4}\rceil,\qquad q=n^{3/4+o(1)}.$$
--   For this second conclusion, one program and pass function per confidence level obey every positive-epsilon bound; they are not reselected for $\varepsilon$ or an individual graph.
--
--   **Formalization Note** The generic clause assumes the three §4 primitive tasks, including SCC decomposition. The specialized clause is unconditional. No leading O-constant is specified by the source. All implicit constants are uniform over $k,p,n$, graph and insertion order.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - encoding: k=ceil(n^(1/4)) gives q=n^(3/4+o(1)) using the available p=n^(1/2+o(1)) → an unconditional quarter-power task specialization with the exact k header and one all-epsilon pass function; reason: the existence of the available primitives is proof work; the specialization is retained as a second conclusion
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Proposition 4.1, printed p.12 (PDF p.13)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Proposition 4.1, printed p.12 (PDF p.13). The uniform k tradeoff and its
ceil(n^(1/4)) specialization are both conclusions; the output is cyclically ordered. -/
theorem proposition_4_1 :
    (∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n →
            ∀ input : List (Fin n × Fin n),
              Solves P input (natCode k) (CycleOutput input.toFinset)
                (workBits C d b n) (tradeoff C 3 false p n k) c n) ∧
    QuarterSpecialization := by sorry

end DigraphDFSStream.Main.Supplement
