-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_prop3_cutoff_problem
-- name    : AdvSellUpgrade.Online.prop3_cutoff_problem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:29.492994+00:00
-- url     : https://prove2.me/theorems/69284fb5-8eb4-4828-9710-06cf3e37e171
-- title:
--   Proof of Proposition 3, OA p. 6 — ψ is increasing and the revenue in the cutoff is maximised at c(λ) with value π(λ)
-- statement:
--   Let $0<\lambda<\mu$ and $\bar c>0$, and let $W_F(\hat c)=\lambda/(\mu(\mu-(1-\hat c/\bar c)\lambda))$, $W_R(\hat c)=\mu W_F(\hat c)/(\mu-\lambda)$. Define
--   $$\psi(\hat c)=\hat c\,\bigl(W_R(\hat c)-W_F(\hat c)\bigr),\qquad g(\hat c)=\frac{\lambda^2\hat c(\bar c-\hat c)}{\mu(\mu-\lambda)\bigl(\mu\bar c-(\bar c-\hat c)\lambda\bigr)} .$$
--   Then:
--   1. $\psi$ is strictly increasing on $[0,\bar c]$;
--   2. $c(\lambda)\in(0,\bar c)$ and $\displaystyle\max_{0<\hat c<\bar c} g(\hat c)=g\bigl(c(\lambda)\bigr)=\pi(\lambda)$;
--   3. $\psi\bigl(c(\lambda)\bigr)=p(\lambda)$.
--
--   Here $p,c,\pi$ are the functions of p. 14. The function $\psi$ maps a cutoff to the price gap $P_s-B_s$ that induces it, and $g(\hat c)+B_s$ is the spot-only revenue written in terms of the cutoff. This one-rate maximisation is the step that the proofs of Propositions 3, 5 and 6 reuse for each state.
--
--   **Formalization Note** The paper proves this for $\lambda_h$ and says "the same logic" gives $\lambda_l$; it is stated here for every rate $\lambda\in(0,\mu)$, which covers both. Part 3 is the paper's "Moreover, $P_s^\star=B_s+p(\lambda_h)$" in cutoff form.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, Online Appendix p. 6, proof of Proposition 3

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Proof of Proposition 3, OA p. 6: for a single rate `λ ∈ (0, µ)`, (i) `ψ(ĉ) = ĉ(W_R(ĉ) − W_F(ĉ))` is
strictly increasing on `[0, c̄]`; (ii) the revenue-in-cutoff function `λ²ĉ(c̄ − ĉ)/(µ(µ − λ)(µc̄ − (c̄ − ĉ)λ))`
attains its maximum over `0 < ĉ < c̄` at `ĉ = c(λ)`, with maximum value `π(λ)` and price gap
`ψ(c(λ)) = p(λ)`. -/
theorem prop3_cutoff_problem (mu cbar lam : ℝ) (hlam : 0 < lam) (hlammu : lam < mu)
    (hcbar : 0 < cbar) :
    StrictMonoOn (fun ch => ch * (WR mu cbar lam ch - WF mu cbar lam ch)) (Set.Icc 0 cbar) ∧
      cFn mu cbar lam ∈ Set.Ioo 0 cbar ∧
      (∀ ch ∈ Set.Ioo 0 cbar, revCut mu cbar lam ch ≤ revCut mu cbar lam (cFn mu cbar lam)) ∧
      revCut mu cbar lam (cFn mu cbar lam) = piFn mu cbar lam ∧
      cFn mu cbar lam * (WR mu cbar lam (cFn mu cbar lam) - WF mu cbar lam (cFn mu cbar lam))
        = pFn mu cbar lam := by sorry

end AdvSellUpgrade.Online
