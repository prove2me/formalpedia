-- Prove2me | Theorems.Thm_DigraphDFSStream_Main_Supplement_lemma_4_3
-- name    : DigraphDFSStream.Main.Supplement.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:57:52.520655+00:00
-- url     : https://prove2.me/theorems/bec722c9-0ac2-428c-9cb4-402bcf6e2cfe
-- title:
--   Lemma 4.3 — strong maximal joining
-- statement:
--   Let $H$ have $m\le n$ vertices, $\mathcal P$ be disjoint simple directed input paths and $T$ disjoint designated sinks. For each integer $1\le k\le n$, there is a uniform semi-streaming program computing a strong maximal joining, with
--   $$q(n,k)\le\left\lceil\frac{2n}{k}\right\rceil+3kp(n)=O(n/k+kp(n)).$$
--   The program works on every edge stream and every admissible input family. Its output contains all three clauses of Definition 4.2, including residual maximality for discarded source suffixes. Memory is semi-streaming and correctness has the prescribed high probability.
--
--   **Formalization Note** The proof bounds Stage 1 by $2n/k$ scans. Each of fewer than $k$ remaining active paths needs one reverse reachability call, one witness scan, and one path call: $2p+1\le3p$ because $p\ge1$. This supplies the displayed explicit pass envelope. This is a resource existence statement, not an implementation or a proof of it.
--
--   Differences from the source:
--   - encoding: semi-streaming algorithms on adversarial insertion-only edge streams → uniform finite programs of the published bit-stack machine, with task parameters in a charged initial register and output charged on every execution prefix; reason: parameters encode only supplied sources, paths, sinks and integers; no graph oracle or free working state is introduced
--   - reading: p bounds subroutines on auxiliary graphs with O(n) vertices; randomized calls are amplified for high probability → a fixed A and reliability exponent D precede p, b and every instance; primitive programs work on at most A*n vertices with failure at most (n+2)^(-D); reason: this is the structured brief's ambient-size reading; selecting D sufficiently large must cover every adaptive primitive call in the proof
--   - encoding: Õ(n) space and uniform O pass bounds, with singleton cases handled directly → memory at most C*(b(n)+(n+1)*L(n+2)^d), fixed logarithmic pass powers using L(n)=ceil(log2 n)+1, integer ceilings and at least one pass; reason: b is the supplied semi-streaming primitive budget; C and d precede p and b; regularization preserves asymptotics and charges initialization at small sizes
--   - encoding: O(n/k+kp) passes; proof supplies at most 2n/k Stage 1 rounds and two primitive calls plus a scan per Stage 2 path → at most ceil(2*n/k)+3*k*p(n) passes; reason: there are fewer than k Stage 2 paths and 2*p+1 <= 3*p for p>=1; no source constant is dropped
--   - reading: the lemma uses the parameter k without stating its range; Section 4 introduces k in Proposition 4.1 as an integer with 1 <= k <= n → the statement holds for every integer k with 1 <= k <= n, k supplied in the charged header, one program for all k; reason: the lemmas are steps of Proposition 4.1's construction and inherit its k; n is the section's vertex count (the size bound in Lemma 4.3)
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), Lemma 4.3, printed p.12 (PDF p.13)

import Definitions.Def_DigraphDFSStream_Main_Supplement_StrongJoining
import Definitions.Def_DigraphDFSStream_Main_Supplement_PrimitiveTasks

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

/-- Lemma 4.3, printed p.12 (PDF p.13). n is an upper bound on the graph's size.
The same program works for all k and every admissible input family. -/
theorem lemma_4_3 :
    ∀ c : ℕ, ∃ A D C d : ℕ, 2 ≤ A ∧ c + 1 ≤ D ∧ 0 < C ∧
      ∀ p b : ℕ → ℕ, (∀ n, 1 ≤ n → 1 ≤ p n) → SemistreamingBits b →
        SectionPrimitives A p b D → ∃ P : StreamProgram,
          SemistreamingBits (workBits C d b) ∧
          ∀ (n m k : ℕ), 1 ≤ n → m ≤ n → 1 ≤ k → k ≤ n →
            ∀ (input : List (Fin m × Fin m))
              (paths : List (List (Fin m))) (sinks : List (Fin m)),
              JoiningInput input.toFinset paths sinks →
              Solves P input (natCode n ++ natCode k ++ familyCode paths ++ vertexCode sinks)
                (JoiningOutput input.toFinset paths sinks)
                (workBits C d b n) (joiningPasses p n k) c n := by sorry

end DigraphDFSStream.Main.Supplement
