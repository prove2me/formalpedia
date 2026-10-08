-- Prove2me | Theorems.Thm_DROOptimal_Continuous_proposition_1_iii_general
-- name    : DROOptimal.Continuous.proposition_1_iii_general
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:05:23.687972+00:00
-- url     : https://prove2.me/theorems/1ae3a504-78d5-425d-b397-8c166b392bc6
-- title:
--   §5, p. 24 — Proposition 1(iii) holds for the generalized relative entropy: I is lower semicontinuous on 𝒫 × 𝒫 (weak topology)
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be compact and let $\mathcal P$ be the Borel probability distributions on $\Xi$ with the topology of weak convergence. The generalized relative entropy (Definition 8)
--   $$
--   (\mathbb P',\mathbb P)\ \mapsto\ I(\mathbb P',\mathbb P)\in[0,+\infty]
--   $$
--   is lower semicontinuous on $\mathcal P\times\mathcal P$ (product topology).
--
--   The paper states that the properties of Proposition 1 hold verbatim in the setting of §5. Together with compactness of $\mathcal P$, lower semicontinuity yields the optimal model in (10) on which the proof of strong optimality (Theorem 10) is built.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 24 (sentence after Definition 8) with p. 12, Proposition 1(iii)

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Proposition 1(iii) in the setting of §5 (p. 24, with p. 12): `I(ℙ′, ℙ)` is jointly lower
semicontinuous on `𝒫 × 𝒫` for the weak topology. -/
theorem proposition_1_iii_general {d : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} (hΞ : IsCompact Ξ) :
    LowerSemicontinuous (fun q : Dist Ξ × Dist Ξ => relEnt q.1 q.2) := by sorry

end DROOptimal.Continuous
