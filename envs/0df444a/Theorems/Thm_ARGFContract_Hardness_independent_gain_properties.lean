-- Prove2me | Theorems.Thm_ARGFContract_Hardness_independent_gain_properties
-- name    : ARGFContract.Hardness.independent_gain_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:15.065331+00:00
-- url     : https://prove2.me/theorems/3162fa58-1afe-46df-bb92-c51d9f791d9d
-- title:
--   Proof of Theorem 1, pp. 7–8 — range, attained maximum, and subadditivity of h
-- statement:
--   Let $G$ be a finite simple graph on $n\ge1$ vertices, and let $h_G(S)=|S|/n$ for independent sets and zero otherwise. Then
--
--   $$0\le h_G(S)\le1,\qquad \max_{S\subseteq V(G)}h_G(S)=\frac{\rho(G)}n,$$
--   $$h_G(A\cup B)\le h_G(A)+h_G(B).$$
--
--   The maximum is attained by an independent set of cardinality $\rho(G)$. This is the complete mathematical statement concerning $h$ in the proof; its polynomial evaluation is included in the separate oracle milestone.
--
--   Differences from the source:
--   - encoding: vertices labelled 1 through n and real expressions in the rational construction → Fin n labels and exact rational expressions, cast to reals when needed; reason: the label bijection sends i to i+1 and rational values embed exactly into the reals
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, pp. 7–8, definition and displayed properties of h; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_IndependentGain

namespace ARGFContract.Hardness

/-- Proof of Theorem 1, pp. 7–8. Polynomial evaluation is M4. -/
theorem independent_gain_properties {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    (∀ S, 0 ≤ independentGain G S ∧ independentGain G S ≤ 1) ∧
    maxSubset (independentGain G) = (G.indepNum : ℚ) / n ∧
    (∃ S : Finset (Fin n), G.IsIndepSet (S : Set (Fin n)) ∧ S.card = G.indepNum ∧
      independentGain G S = maxSubset (independentGain G)) ∧
    (∀ A B, independentGain G (A ∪ B) ≤ independentGain G A + independentGain G B) := by sorry

end ARGFContract.Hardness
