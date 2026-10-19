-- Prove2me | Theorems.Thm_DigitalPrivacy_Welfare_proposition_5_i
-- name    : DigitalPrivacy.Welfare.proposition_5_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:50.529185+00:00
-- url     : https://prove2.me/theorems/ac06a1da-6ed6-4400-9cb5-f9de0b22ce06
-- title:
--   Proposition 5(i), Online App. p. 8 — for fixed protection C, a purely usage-driven business's data collection is socially optimal
-- statement:
--   Work in the model of *DigitalPrivacy.Welfare.Setting* with a purely usage-driven business, $P=0$, so that the profit is $\Pi(\xi,C)=\bar a^*(\xi,C)-\psi C$. Assume the printed ranges $0\le\beta<1$, $0\le\rho<1$, $\psi\ge0$ and $0\le\alpha\le1$ (the case $\alpha=0$ is allowed). Fix a protection level $C\ge0$ and a collection level $\xi\in[0,1]$. Then $\xi$ maximizes the business's profit over data collection at protection $C$ if and only if it maximizes the planner's objective at protection $C$:
--   $$
--   \Bigl(\forall \xi'\in[0,1]:\ \Pi(\xi',C)\le\Pi(\xi,C)\Bigr)\iff\Bigl(\forall \xi'\in[0,1]:\ W(\xi',C)\le W(\xi,C)\Bigr).
--   $$
--
--   In words: for a given level of data protection, the data collection chosen by a purely usage-driven business is socially optimal. In the proof of Theorem 2 this is what lets the comparison of the two optima for $P=0$ run through a single best-response map in $\xi$.
--
--   **Formalization Note.** The paper states Proposition 5 for a general profit function $\Phi(\bar a,\xi\bar a)-K(C)$ (Online App. C.5); for the linear profit (2), "purely usage-driven" is $P=0$. The paper's proof concludes $\xi^*(C)=\xi^W(C)$, i.e. the two sets of maximizers in $\xi$ coincide, which is the equivalence stated here. Only the first claim of Proposition 5(i) (its first two sentences) is formalized.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), Online App. C.5, p. 8, Proposition 5(i), first claim (proof Online App. p. 9)

import Mathlib
import Definitions.Def_DigitalPrivacy_Welfare_Setting

namespace DigitalPrivacy.Welfare
theorem proposition_5_i (β ρ ψ α : ℝ) (h : PrintedBounds β ρ ψ 0 α) (C : ℝ) (hC : 0 ≤ C)
    (ξ : ℝ) (hξ : ξ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, Pi β ρ ψ 0 ξ' C ≤ Pi β ρ ψ 0 ξ C) ↔
      (∀ ξ' ∈ Set.Icc (0 : ℝ) 1, W β ρ ψ 0 α ξ' C ≤ W β ρ ψ 0 α ξ C) := by sorry
end DigitalPrivacy.Welfare
