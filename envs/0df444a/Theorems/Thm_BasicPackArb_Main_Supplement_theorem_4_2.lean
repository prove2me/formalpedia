-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_theorem_4_2
-- name    : BasicPackArb.Main.Supplement.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:03:42.429501+00:00
-- url     : https://prove2.me/theorems/7b09acfb-27de-4713-9eb5-2a4d33c09896
-- title:
--   Theorem 4.2 — a polynomial-time packing or an actual obstruction
-- statement:
--   For every finite rooted digraph $(D,S,\pi)$ and every matroid $M$ on $S$, given a correct rank oracle for $M$, one uniform algorithm produces one of the following: a full $M$-basic arborescence packing; a vertex $v$ with $S_v$ dependent; or a nonempty set $X\subseteq V$ such that $\rho_D(X)+r_M(S_X)<r_M(S)$. If $L$ is the explicit graph/root input size, then for a single program $P$ and polynomial $p$, independent of the instance and oracle,
--
--   $$\forall(D,S,\pi,M,O),\quad T_{P,O}(D,S,\pi)\le p(L).$$
--
--   The output encodes every tree's vertex and arc membership, or the actual obstructing vertex or vertex set. The oracle returns only ranks of explicitly constructed root subsets. Rank replies must be correct for all subsets. Runtime includes bit operations, scalar operations, query construction, calls and output construction; $L$ contains no exponential rank table. This constructive companion supplies actual witnesses rather than a feasibility assertion.
--
--   Differences from the source:
--   - encoding: an algorithm running in polynomial time with a rank oracle → one finite scalar program and a natural-coefficient polynomial quantified before all labelled instances and correct rank oracles; reason: labels cover every finite input; the interpreter charges ordinary work, explicit query construction and output; it supplies no packing or minimization primitive
--   - encoding: finite digraphs with roots and the three possible witnesses → labels Fin n, Fin m, Fin t, an explicit endpoint/placement list and a tagged output stream; reason: every finite instance has a labelling, no simplicity, nonemptiness or positive-rank restriction is introduced, and exact output masks determine the packing
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 6, Theorem 4.2

import Definitions.Def_BasicPackArb_Main_Supplement_AlgorithmIO

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Theorem 4.2, pp. 6--7. A single program and polynomial precede all instances and oracles. -/
theorem theorem_4_2 :
    ∃ (code : Program) (p : Polynomial ℕ),
      ∀ (n m t : ℕ) (I : Instance n m t) (M : Matroid (Fin t)), M.E = Set.univ →
        ∀ oracle : Finset (Fin t) → ℕ, Instance.rankOracleCorrect M oracle →
          ∃ out : List ℕ,
            Machine.ComputesWithin (K := ℚ) code rationalSize oracle I.input [] (p.eval I.size) out ∧
            I.ValidOutput M out := by sorry

end BasicPackArb.Main.Supplement
