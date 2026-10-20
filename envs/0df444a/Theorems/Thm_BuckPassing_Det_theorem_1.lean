-- Prove2me | Theorems.Thm_BuckPassing_Det_theorem_1
-- name    : BuckPassing.Det.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:33.03598+00:00
-- url     : https://prove2.me/theorems/65e68b55-9c3f-4a35-952a-7e8686876f8e
-- title:
--   Theorem 1, pp. 9–10 — the cycle-length sum is a generalized ordinal potential
-- statement:
--   For any finite loopless directed graph with a nonempty out-neighborhood at every vertex, and any initial probability distribution $\mu$, define $\Psi$ by summing $|V|-|C|$ over the distinct cycles $C$ induced by a pure strategy profile. Then every profitable unilateral deviation strictly reduces $\Psi$:
--
--   $$\Psi(s)=\sum_{C\in\mathcal C(s)}(|V|-|C|),\qquad c_i(x,s_{-i})<c_i(s)\ \Longrightarrow\ \Psi(x,s_{-i})<\Psi(s).$$
--
--   The potential is independent of the initial distribution. This is the first assertion of Theorem 1 and is the structural ingredient for the prior-free equilibrium of Theorem 2.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, pp. 9–10, Theorem 1, first assertion and equation (10)

import Mathlib
import Definitions.Def_BuckPassing_Det_Model

namespace BuckPassing.Det

/-- Theorem 1, first assertion: equation (10) is a generalized ordinal potential. -/
theorem theorem_1 {V : Type*} [Fintype V] [DecidableEq V]
    (G : BPGraph V) (mu : V → ℝ) (hmu : IsDistribution mu) :
    IsGenOrdPotential (cost G mu) (Psi G) := by sorry

end BuckPassing.Det
