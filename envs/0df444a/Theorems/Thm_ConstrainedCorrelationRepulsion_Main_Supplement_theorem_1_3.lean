-- Prove2me | Theorems.Thm_ConstrainedCorrelationRepulsion_Main_Supplement_theorem_1_3
-- name    : ConstrainedCorrelationRepulsion.Main.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:07:17.791199+00:00
-- url     : https://prove2.me/theorems/ba5b538a-f538-4bdc-9f4c-4af84b4849a6
-- title:
--   Theorem 1.3 — exact c-to-c transfer including running time
-- statement:
--   Fix any real $c>1$, let $k=\lceil c/[2(c-1)]\rceil$ and $c'=k+1$. If one finite word program is a pointwise $c$-approximation for cluster deletion, with an at-most-$N$ worst-case time envelope $f(N)$, then there is a finite word program giving a $c$-approximation for vertex cover on every $n$-vertex graph in time
--
--   $$O\bigl(f(c'n^2)+n^4\bigr).$$
--
--   More precisely, a positive constant $C$, depending only on $c$ and the fixed machine convention, works uniformly over the deletion program, $f$, $n$ and the graph; the cover program's budget is at most $C(f(c'n^2)+\max\{1,n\}^4)$. Every supported output is a vertex cover of size at most $c\tau(G)$. The envelope $f$ is arbitrary and need not be polynomial or supplied as a monotone function. Runtime is a conclusion about executions. The two deletion calls are charged through the resulting finite program, rather than treated as free oracles.
--
--   This exact-ratio transfer supplies both hardness clauses through the cited vertex-cover results. The source construction removes each endpoint of an input edge in turn, complements, joins a large universal clique, chooses the smaller deletion output, and extracts the clique; complete and edgeless inputs have direct outputs.
--
--   Differences from the source:
--   - encoding: ordinary adjacency-matrix word algorithms and O(f(c′n²)+n⁴) → finite charged word executions with an at-most-size envelope and max(1,n)⁴ at the empty input; reason: this gives uniform O-notation constants, charges both calls, avoids assuming monotonicity of f, and includes the source empty graph
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.3, printed p.2 (PDF p.3), repeated statement and proof printed pp.36–37 (PDF pp.37–38)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_WordAlgorithms

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- Exact c-to-c transfer, including the source's arbitrary time envelope. C depends only
on c and fixed machine conventions, not on the input, algorithm or envelope. The two calls
are charged within the conclusion, not granted as zero-cost oracles. Empty inputs are covered
by max 1 n in the uniform O-notation convention. -/
theorem theorem_1_3 (c : ℝ) (hc : 1 < c) :
    ∃ C : ℕ, 0 < C ∧ ∀ code : Program, ∀ f : ℕ → ℕ,
      DeletionAlgorithm code c f →
      ∃ coverCode : Program, ∀ n (G : Graph n),
        ∃ B ≤ C * (f (blowupCoefficient c * n^2) + (max 1 n)^4),
          CoverRun coverCode G c B := by sorry

end ConstrainedCorrelationRepulsion.Main.Supplement
