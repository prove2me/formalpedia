-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_weighted_stack_qptas
-- name    : EdgeSublinearMWIS.Main.weighted_stack_qptas
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-17T15:58:26.50963+00:00
-- url     : https://prove2.me/theorems/594fba4c-68e2-4b89-a782-a907ba20e3bd
-- title:
--   Finite stack implementation of the weighted QPTAS
-- statement:
--   For every hereditary graph class $\mathcal C$ with strongly edge-sublinear separators, one finite deterministic stack program solves maximum-weight independent set approximately on all graphs of that class, all signed rational weights, and all rational $0<\varepsilon<1$.
--
--   There is a universal positive integer $q$ such that each class has one program and constants $K>0$, $d>0$ with returned independent set $I$ and actual stack-machine running time $t$ satisfying
--   $$w(I)\ge(1-\varepsilon)\alpha_w(G),\qquad t\le K\exp\!\bigl(K(\varepsilon^{-1}\log_2\max\{2,n\})^d\bigr)+K(\ell+1)^q.$$
--   The graph, weights and accuracy are the only input. The empty independent set is allowed, arbitrary positive-denominator rational encodings are accepted, and the bound includes reading and preprocessing these encodings. This is the finite stack implementation stage of Theorem 2; conversion to the mission's local binary machine is a separate simulation obligation.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 and explanatory paragraph, p.2; repeated proof p.20, p.2 (PDF p.2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf; finite stack implementation stage, using the algorithms of Sections 5–6 before their polynomial local-bit simulation.

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- Finite stack implementation of the weighted scheme before local bit simulation. -/
theorem weighted_stack_qptas :
    ∃ q : ℕ, 0 < q ∧ ∀ C : GraphClass, StronglyEdgeSublinear C →
      ∃ (P : Program) (K : ℝ) (d : ℕ), 0 < K ∧ 0 < d ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : Fin n → RationalCode)
          (ε : RationalCode), C n G → 0 < ε.value → ε.value < 1 →
          ∃ (I : Finset (Fin n)) (s : ℕ),
            Runs P (weightedInput G w ε) (mask I) s ∧
            G.IsIndepSet (I : Set (Fin n)) ∧
            (1 - (ε.value : ℝ)) * weightedAlpha G (fun v => (w v).value) ≤
              ∑ v ∈ I, ((w v).value : ℝ) ∧
            (s : ℝ) ≤ K * Real.exp
              (K * (((ε.value : ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1 : ℝ) ^ q := by sorry

end EdgeSublinearMWIS.Main
