-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_example_1_eq_3
-- name    : BayesGroupHard.VertexCover.example_1_eq_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:23.594727+00:00
-- url     : https://prove2.me/theorems/3f694299-b2da-4971-a822-a90f2b261086
-- title:
--   Example 1, (3), p. 8 — time-zero actions reveal informative signals and $\phi_{i,1} = \sum_{j \in \mathcal N_i} \lambda_j$
-- statement:
--   Consider any network of the binary action model and an agent $i$ all of whose neighbours $j \in \mathcal N_i$ (herself included) have informative signals:
--   $$0 < \mathbb P_{j,0}(1) < \mathbb P_{j,1}(1) < 1.$$
--   Then on every signal profile $s$:
--
--   1. agent $i$'s time-zero action is her signal, $a_{i,0} = s_i$;
--   2. her time-zero log-belief ratio is $\phi_{i,0} = \log\bigl(\mathbb P_{i,1}(s_i)/\mathbb P_{i,0}(s_i)\bigr)$;
--   3. her time-one log-belief ratio is the sum of her neighbours' signal log-likelihood ratios,
--   $$\phi_{i,1} = \sum_{j \in \mathcal N_i} \log\frac{\mathbb P_{j,1}(s_j)}{\mathbb P_{j,0}(s_j)} = \sum_{j\in\mathcal N_i} \lambda_j. \tag{3}$$
--
--   This is the paper's illustration of the model in the first two rounds; the reduction of Appendix A uses it for the vertex and edge agents.
--
--   **Formalization Note.** The paper assumes $\mathbb P_{i,1}(1) > \mathbb P_{i,0}(1)$; the bounds $0 < \mathbb P < 1$ are added so that all the logarithms are of positive numbers. In (3) the paper writes $a_{j,0}$ inside the sum, which equals $s_j$ by the first claim applied to $j$.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 8, Example 1, (3)

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- Example 1, (3), p. 8: for an agent `i` all of whose neighbours (herself included) have
informative signals `0 < P_{j,0}(1) < P_{j,1}(1) < 1`, the time-zero action reveals the signal,
`φ_{i,0} = log(P_{i,1}(s_i)/P_{i,0}(s_i))`, and `φ_{i,1} = Σ_{j ∈ N_i} λ_j`. -/
theorem example_1_eq_3 {Ag : Type} [Fintype Ag] [DecidableEq Ag] (N : BinNet Ag) (i : Ag)
    (hinf : ∀ j ∈ N.nbr i, 0 < N.p j false ∧ N.p j false < N.p j true ∧ N.p j true < 1)
    (s : Ag → Bool) :
    act N 0 i s = s i ∧
    logBelief N 0 i s = Real.log (sig N i true (s i) / sig N i false (s i)) ∧
    logBelief N 1 i s = ∑ j ∈ N.nbr i, Real.log (sig N j true (s j) / sig N j false (s j)) := by sorry

end BayesGroupHard.VertexCover
