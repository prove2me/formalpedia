-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_theorem_1_2
-- name    : DigraphDFSStream.Main.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:02:25.709713+00:00
-- url     : https://prove2.me/theorems/b2fc6420-bc72-4d2e-9948-61d1b016e2c8
-- title:
--   Theorem 1.2 — directed cycle separators (corrected: nonempty input)
-- statement:
--   Let $G$ be a directed graph on $n\ge1$ vertices. Let $p(n)\ge1$ bound semi-streaming single-source reachability and directed $s,t$-path construction on the auxiliary graphs of size $O(n)$. There is a randomized semi-streaming program which, with high probability, returns a directed cycle separator in cyclic vertex order using
--   $$q=\widetilde O\!\left(\sqrt{n\,p(n)}\right)\text{ passes}.$$
--   In particular, independently of a supplied primitive package, there is such a program using
--   $$q=n^{3/4+o(1)}\text{ passes}.$$
--   Both clauses include semi-streaming bits, all-tape resource bounds and the actual execution's high-probability output guarantee. The same specialized program and pass function obey $O(n^{3/4+\varepsilon})$ for every $\varepsilon>0$. The generic square root covers the entire product $n p(n)$; no assumption $p(n)\le n$ is made.
--
--   **Formalization Note** SCC decomposition is not a hypothesis. Its construction from reachability, including its logarithmic overhead, remains part of the proof. All constants, the auxiliary-size factor and the primitive reliability exponent are chosen before $p,b$ and every graph. The empty graph is excluded because it has neither a simple cycle nor a vertex for a singleton, while §4 treats singletons directly.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - correction: given a directed graph on n nodes, with no nonempty-input restriction → cycle correctness is required for n>=1; reason: at n=0 Definition 2.2 has neither a simple directed cycle nor a singleton vertex, so a cycle separator cannot exist; this excludes exactly the impossible empty input
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Theorem 1.2, printed p.2 (PDF p.3); repeated printed p.17 (PDF p.18), proved printed pp.17–18 (PDF pp.18–19)

import Definitions.Def_DigraphDFSStream_Main_Supplement_SeparatorTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Theorem 1.2, printed p.2 (PDF p.3), repeated p.17 (PDF p.18).
Corrected only by excluding n=0, where Definition 2.2 admits no cycle separator.
SCC decomposition is derived in the proof, never assumed here. No upper bound p≤n is imposed. -/
theorem theorem_1_2 :
    (∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        ReachPathPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          HasStreamingBounds P (workBits C d b) (rootPasses C d p) ∧
          CycleHighProbability P c) ∧
    CycleSubpower := by sorry

end DigraphDFSStream.Main.Supplement
