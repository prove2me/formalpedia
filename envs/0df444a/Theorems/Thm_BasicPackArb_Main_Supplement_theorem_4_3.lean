-- Prove2me | Theorems.Thm_BasicPackArb_Main_Supplement_theorem_4_3
-- name    : BasicPackArb.Main.Supplement.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:05:24.31037+00:00
-- url     : https://prove2.me/theorems/8738d257-64d5-4e27-bc4e-ee6f3bd89c46
-- title:
--   Theorem 4.3 — polynomial-time minimum-cost basic arborescence packing
-- statement:
--   Let $(D,S,\pi)$ be a finite rooted digraph and $M$ a matroid on $S$ given by a correct rank oracle, and let $c:A\to\mathbb Q$ be an arbitrary signed rational cost function. If an $M$-basic arborescence packing exists, a uniform program returns an actual feasible family $T$ with
--
--   $$\operatorname{cost}_c(T)\le\operatorname{cost}_c(U)\quad\text{for every feasible packing }U,\qquad T_{P,O}(D,S,\pi,c)\le q(L_c).$$
--
--   Cost is the sum of $c(a)$ over the union of the family's arcs. $L_c$ is the graph/root input size plus the numerator and denominator encoding lengths of all costs, and the runtime counts rational arithmetic by bit length, rank queries, query construction and output. The program and the polynomial $q$ are chosen before all instances, matroids, oracles and cost functions. No solution or feasibility certificate is placed in the input; feasibility is solely the source's promise on which an optimal output is required. This is the optimization companion of the directed existence theorem.
--
--   **Formalization Note** The paper proves this theorem with the ellipsoid method, whose polynomial-time guarantee is in the bit model on finitely encoded data; costs are therefore rational, with arbitrary signs. A unit-cost real-arithmetic (strongly polynomial) version is not claimed by the source and is not stated.
--
--   Differences from the source:
--   - encoding: an algorithm running in polynomial time with a rank oracle → one finite scalar program and a natural-coefficient polynomial quantified before all labelled instances and correct rank oracles; reason: labels cover every finite input; the interpreter charges ordinary work, explicit query construction and output; it supplies no packing or minimization primitive
--   - encoding: a cost function c on the arcs and polynomial time (proved with the ellipsoid method of Grötschel, Lovász and Schrijver) → arbitrary signed rational costs, exact rational arithmetic charged by bit length, and a polynomial bound in the input size including every cost encoding length; reason: polynomial time in the ellipsoid-method sense the proof uses is measured on finitely encoded (rational) data; signs are unrestricted and no exponent is fixed
-- source:
--   Durand de Gevigney, Nguyen, Szigeti, Basic Packing of Arborescences, arXiv:1207.1985v1, p. 7, Theorem 4.3

import Definitions.Def_BasicPackArb_Main_Supplement_AlgorithmIO

set_option autoImplicit false

namespace BasicPackArb.Main.Supplement

/-- Theorem 4.3, p. 7. Arbitrary signed rational costs in the standard bit-complexity model
(the ellipsoid-method setting of the proof): the runtime bound is a polynomial in the input size,
cost encoding lengths included. The uniform program receives no packing or feasibility
certificate as input. -/
theorem theorem_4_3 :
    ∃ (code : Program) (q : Polynomial ℕ),
      ∀ (n m t : ℕ) (I : Instance n m t) (M : Matroid (Fin t)), M.E = Set.univ →
        ∀ (oracle : Finset (Fin t) → ℕ), Instance.rankOracleCorrect M oracle →
          ∀ c : Fin m → ℚ,
            (∃ T, IsBasicPacking I.digraph I.placement M T) →
            ∃ out : List ℕ,
              Machine.ComputesWithin code rationalSize oracle I.input (List.ofFn c)
                (q.eval (I.rationalInputSize c)) out ∧ I.OptimalOutput M c out := by sorry

end BasicPackArb.Main.Supplement
