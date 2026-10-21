-- Prove2me | Theorems.Thm_BuckPassing_Det_eq_6
-- name    : BuckPassing.Det.eq_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:22.326537+00:00
-- url     : https://prove2.me/theorems/9845cea0-d161-454b-8887-5a6adcbf4725
-- title:
--   Equation (6), p. 7 — long-run visit frequencies and player costs
-- statement:
--   Fix a pure profile $s$ and write $f_s(i)=s_i$. For every initial vertex $j$ and player $i$, the frequency of visits to $i$ along the orbit of $j$ converges. Its limit is $1/|C_i|$ if $i$ lies on a cycle $C_i$ and $j$ lies in that cycle's basin, and is zero otherwise. Consequently, for any real weight vector $\mu$,
--
--   $$c_i(s)=\begin{cases}\displaystyle\frac{\sum_{j\in A_i}\mu_j}{|C_i|},&i\in C_i,\\[4pt]0,&i\text{ is transient},\end{cases}$$
--
--   where $A_i$ is the basin of $C_i$. For an initial probability distribution, this is the paper's formula $c_i(s)=\mu_s^{\ell(i)}\delta_i(s)/|C_s^{\ell(i)}|$.
--
--   The convergence statement makes the limit in the definition of cost well-defined and is reusable for finite deterministic dynamics beyond this game.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, pp. 6–7, §3, equation (6), with the orbit-limit claim immediately preceding it

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

open Classical Finset Filter

/-- Equation (6), including existence and value of the limit in equation (3). -/
theorem eq_6 {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) (mu : V → ℝ) (s : ∀ i, Strat G i) :
    (∀ j i : V,
      Tendsto (fun T : ℕ =>
        (((Finset.Icc 1 T).filter (fun t => (toMap s)^[t] j = i)).card : ℝ) / T)
        atTop
        (nhds (if i ∈ Function.periodicPts (toMap s) ∧
                   j ∈ basin (toMap s) (cycleOf (toMap s) i)
               then (1 : ℝ) / (cycleOf (toMap s) i).card else 0))) ∧
    (∀ i : V, cost G mu i s =
      if i ∈ Function.periodicPts (toMap s) then
        basinMass mu (toMap s) (cycleOf (toMap s) i) /
          (cycleOf (toMap s) i).card
      else 0) := by sorry

end BuckPassing.Det
