-- Prove2me | Theorems.Thm_BuckPassing_Det_deviation_cases
-- name    : BuckPassing.Det.deviation_cases
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:14.119623+00:00
-- url     : https://prove2.me/theorems/e2f099e8-8ac5-4a5d-8b89-22684da14633
-- title:
--   §3.1, p. 9 — profitable deviations lengthen or remove a cycle
-- statement:
--   Fix an initial probability distribution $\mu$ and a profile $s$. If player $i$ can lower her cost by changing her chosen out-neighbor to $x$, then $i$ lies on a cycle $C_i$ whose basin $A_i$ has positive initial mass. Moreover, either $x\in A_i\setminus C_i$ and the new cycle through $i$ is strictly longer than $C_i$, or $x\notin A_i$:
--
--   $$c_i(x,s_{-i})<c_i(s)\ \Longrightarrow\ i\in C_i,\quad \mu(A_i)>0,\quad [\,x\in A_i\setminus C_i\ \land\ |C_i'|>|C_i|\,]\ \lor\ [\,x\notin A_i\,].$$
--
--   These two cases are the structural classification used immediately before Theorem 1.
--
--   **Formalization Note** The paper's phrase “so that the cycle becomes longer” is encoded as part of the first case. A move into $A_i\setminus C_i$ alone need not lengthen the cycle.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, p. 9, §3.1, (d1) and (d2)

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

open Classical

/-- §3.1, p. 9: the two forms of a profitable unilateral deviation. -/
theorem deviation_cases {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu)
    (s : ∀ i, Strat G i) (i : V) (x : Strat G i)
    (hprofit : cost G mu i (Function.update s i x) < cost G mu i s) :
    i ∈ Function.periodicPts (toMap s) ∧
    0 < basinMass mu (toMap s) (cycleOf (toMap s) i) ∧
    ((x.1 ∈ basin (toMap s) (cycleOf (toMap s) i) \ cycleOf (toMap s) i ∧
        (cycleOf (toMap s) i).card <
          (cycleOf (toMap (Function.update s i x)) i).card) ∨
      (x.1 ∉ basin (toMap s) (cycleOf (toMap s) i) ∧
        i ∉ Function.periodicPts (toMap (Function.update s i x)))) := by sorry

end BuckPassing.Det
