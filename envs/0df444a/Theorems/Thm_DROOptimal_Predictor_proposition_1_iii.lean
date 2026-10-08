-- Prove2me | Theorems.Thm_DROOptimal_Predictor_proposition_1_iii
-- name    : DROOptimal.Predictor.proposition_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:04.863076+00:00
-- url     : https://prove2.me/theorems/f5f64f54-0ef9-4b94-b7ca-e2a62d951815
-- title:
--   Proposition 1(iii), p. 12 — the relative entropy I(ℙ′,ℙ) is lower semicontinuous on 𝒫 × 𝒫
-- statement:
--   Let $\mathcal P$ be the probability simplex on $\Xi=\{1,\dots,d\}$, with the topology inherited from $\mathbb R^d$, and $I(\mathbb P',\mathbb P)\in[0,\infty]$ the relative entropy (Definition 5, with $0\log(0/p)=0$ and $p'\log(p'/0)=+\infty$ for $p'>0$). Then
--   $$
--   (\mathbb P',\mathbb P)\ \longmapsto\ I(\mathbb P',\mathbb P)\quad\text{is lower semicontinuous on }\mathcal P\times\mathcal P .
--   $$
--
--   Lower semicontinuity makes the relative entropy balls $\{\mathbb P: I(\mathbb P',\mathbb P)\le r\}$ closed, hence compact, which is why the supremum defining $\hat c_r$ in (10) is attained.
--
--   **Formalization Note** The function is `EReal`-valued and $\mathcal P\times\mathcal P$ carries the product of the subspace topologies.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 12, Proposition 1(iii)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Proposition 1(iii) (Lower semicontinuity), p. 12: the relative entropy I(ℙ′, ℙ) is lower
semicontinuous in (ℙ′, ℙ) ∈ 𝒫 × 𝒫 (product of the relative topologies of 𝒫). -/
theorem proposition_1_iii {d : ℕ} :
    LowerSemicontinuous (fun q : Δ d × Δ d => relEntropy q.1 q.2) := by sorry

end DROOptimal.Predictor
