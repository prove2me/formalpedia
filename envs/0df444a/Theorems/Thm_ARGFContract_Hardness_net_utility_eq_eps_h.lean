-- Prove2me | Theorems.Thm_ARGFContract_Hardness_net_utility_eq_eps_h
-- name    : ARGFContract.Hardness.net_utility_eq_eps_h
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:49.010194+00:00
-- url     : https://prove2.me/theorems/dfe38cef-5512-4cc0-ac95-c6a164bf7237
-- title:
--   Proof of Theorem 1, p. 9 — nonnegative costs and the identity µ = εh
-- statement:
--   For a finite simple graph $G$ on $n\ge1$ vertices, use the constructed gain $f_G$ and costs $c_i=p_i$. Then the costs are nonnegative and
--
--   $$\mu_G(S)=\varepsilon_nh_G(S)\quad\text{for every }S\subseteq V(G),\qquad \max_S\mu_G(S)=\varepsilon_n\frac{\rho(G)}n.$$
--
--   The optimum is the attained maximum over all subsets. The identity retains the entire net-utility objective, rather than assuming an independent-set equivalence as a hypothesis.
--
--   Differences from the source:
--   - encoding: vertices labelled 1 through n and real expressions in the rational construction → Fin n labels and exact rational expressions, cast to reals when needed; reason: the label bijection sends i to i+1 and rational values embed exactly into the reals
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, p. 9, c_i=p_i and net-utility display; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_RankConstruction

namespace ARGFContract.Hardness

/-- Proof of Theorem 1, p. 9: costs are nonnegative and utility is epsilon h. -/
theorem net_utility_eq_eps_h {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    (∀ i : Fin n, 0 ≤ rankCompetency i) ∧
    (∀ S, netUtility (graphGain G) rankCompetency S = epsilon n * independentGain G S) ∧
    maxSubset (fun S => netUtility (graphGain G) rankCompetency S) =
      epsilon n * ((G.indepNum : ℚ) / n) := by sorry

end ARGFContract.Hardness
