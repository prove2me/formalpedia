-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_3
-- name    : EndogBudgetAds.Equilibrium.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:46.453986+00:00
-- url     : https://prove2.me/theorems/ac771103-1f96-4e8f-86f0-c14c4f39af08
-- title:
--   Lemma 3, p. 24 (with the added hypothesis E_j(σ*_j); the printed statement is false) — deviating does not raise the modified profit
-- statement:
--   Fix a bidder $j$, an allocation rule of the ad network, and an admissible deviation $\sigma_j$, while every other bidder plays $\sigma^*$. Then almost surely, on the event $E_j(\sigma_j) \cap E_j(\sigma^*_j)$,
--   $$\tilde\pi_j(\sigma_j, \sigma^*_{-j}) \le \tilde\pi_j(\sigma^*_j, \sigma^*_{-j}).$$
--
--   This is the key lemma of the paper: on a typical valuation profile, no unilateral deviation increases the deviating bidder's modified profit.
--
--   **Formalization Note** The paper's Lemma 3 assumes only $E_j(\sigma_j)$, and in that form it is false. An instance with the paper's budgets (3): $m = 3$, $n = 2$, $\theta \approx (2.6146, 2.5365, 2.7593)$, $\delta = 10^{-3}$, shaded valuations $W = [[4.3791, 0.7167, 0.4836], [4.1297, 5.0756, 3.4230]]$ (rows items, column $0$ bidder $j$), and a deviation bidding $(4.3791, 5.4805)$. Then $E_j(\sigma_j)$ holds and $E_j(\sigma^*_j)$ fails; under $\sigma^*$ bidder 1's budget $B^*_1 \approx 1.467 < \bar\Psi_1 = 4.13$ binds, and $\tilde\pi_j/(1+r_j)$ is at most $0.4202$ under $\sigma^*$ but at least $2.7165$ under the deviation, for every optimal selection. Every condition is strict, so this happens with positive probability. The proof's step "bidder $j$ wins these same items under σ*" (p. 27) needs the σ* allocation to be greedy, which Lemma 6 gives on $E_j(\sigma^*_j)$; hence the added hypothesis. The downstream Lemma 5 survives: the complement of $E_j(\sigma_j) \cap E_j(\sigma^*_j)$ has probability at most $2/m^{6\vartheta-1}$ by Lemma 7, and the resulting factor $\sqrt 2$ in Lemma 15's argument still fits in $3\vartheta/m^{3\vartheta/2}$ for $m \ge e^{3\vartheta+1}$.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 24, Lemma 3 (proof pp. 26–27), corrected by the hypothesis E_j(σ*_j)

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 3, p. 24, with the added hypothesis `E_j(σ*_j)` (the printed statement, with `E_j(σ_j)`
alone, is false): almost surely on `E_j(σ_j) ∩ E_j(σ*_j)`, a unilateral deviation `σ_j` of bidder `j`
does not raise her modified profit, `π̃_j(σ_j, σ*_{−j}) ≤ π̃_j(σ*)`. -/
theorem lemma_3 (M : Market) (hM : M.Standing) (alloc : AllocRule M) (halloc : IsAllocRule M alloc)
    (j : Fin M.m) (σj : Strategy M.n) (hσj : σj.Admissible) :
    ∀ᵐ V ∂ valLaw M, V ∈ EventJ M j σj → V ∈ EventJ M j (sigmaStar M j) →
      modProfit M alloc (deviate (sigmaStar M) j σj) j V ≤
        modProfit M alloc (sigmaStar M) j V := by sorry

end EndogBudgetAds.Equilibrium
