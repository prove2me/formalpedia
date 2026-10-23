-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_perturbed_gittins_set_closed
-- name    : DiscreteSearchGame.Optimal.perturbed_gittins_set_closed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:45.595828+00:00
-- url     : https://prove2.me/theorems/a7660175-a2d0-47a0-a195-84cdb4736f90
-- title:
--   Appendix A, Proof that S̄(ε) is closed, pp. 40, 46–49 — the payoff vectors of Gittins sequences against 𝒫(ε) form a closed set
-- statement:
--   Let $\epsilon\in(0,1/n)$. The set of payoff vectors of all Gittins search sequences against hiding strategies that put probability at least $\epsilon$ on every box,
--   $$\bar S(\epsilon)=\{V(\xi):\ \xi\in\mathcal C_p,\ p\in\mathcal P(\epsilon)\}\subset\mathbb R^n,$$
--   is closed.
--
--   Since $\bar S(\epsilon)$ differs from the payoff set $S(\epsilon)$ of the perturbed game $G(\epsilon)$ by the finitely many vectors of the pseudo-strategies $\zeta_i(\epsilon)$, this gives the closedness of $S(\epsilon)$ on which Lemma 4 rests.
--
--   **Formalization Note.** Every $V_i(\xi)$ here is finite, so the vectors are taken in $\mathbb R^n$ via `toReal`.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 40 and pp. 46–49, Appendix A, Proof that S̄(ε) is closed

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Appendix A, Proof that `S̄(ε)` is closed, pp. 40 and 46–49: for `ε ∈ (0, 1/n)` the set
`S̄(ε) = {V(ξ) : ξ ∈ 𝒞_p, p ∈ 𝒫(ε)}` is closed. -/
theorem perturbed_gittins_set_closed {n : ℕ} (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (ε : ℝ) (hε : 0 < ε) (hεn : ε < 1 / (n : ℝ)) :
    IsClosed (perturbedGittinsSet t q ε) := by sorry

end DiscreteSearchGame.Optimal
