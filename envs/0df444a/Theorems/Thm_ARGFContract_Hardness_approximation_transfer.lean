-- Prove2me | Theorems.Thm_ARGFContract_Hardness_approximation_transfer
-- name    : ARGFContract.Hardness.approximation_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:45.105243+00:00
-- url     : https://prove2.me/theorems/482281d6-d2d0-463d-8ef1-00c61fc2147e
-- title:
--   Proof of Theorem 1, p. 9 — transfer of the same approximation factor
-- statement:
--   Let $G$ have $n\ge1$ vertices, let $\alpha>0$, and let $S\subseteq V(G)$ satisfy the approximation guarantee for the constructed net-utility instance:
--
--   $$\alpha\mu_G(S)\ge\max_T\mu_G(T).$$
--
--   Then
--
--   $$S\text{ is independent in }G,\qquad \alpha|S|\ge\rho(G).$$
--
--   This transfers the factor without changing the ground-set size. It applies to the exact case, constant factors, and the full factor $n^{1-\delta}$ used in the source remark.
--
--   Differences from the source:
--   - encoding: vertices labelled 1 through n and real expressions in the rational construction → Fin n labels and exact rational expressions, cast to reals when needed; reason: the label bijection sends i to i+1 and rational values embed exactly into the reals
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, p. 9, reduction equivalence and Remark; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_RankConstruction

namespace ARGFContract.Hardness

/-- Proof of Theorem 1, p. 9, Remark: the same factor transfers without loss. -/
theorem approximation_transfer {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (α : ℝ) (hα : 0 < α) (S : Finset (Fin n))
    (happrox : α * (netUtility (graphGain G) rankCompetency S : ℝ) ≥
      (maxSubset (fun T => netUtility (graphGain G) rankCompetency T) : ℝ)) :
    G.IsIndepSet (S : Set (Fin n)) ∧ α * (S.card : ℝ) ≥ (G.indepNum : ℝ) := by sorry

end ARGFContract.Hardness
