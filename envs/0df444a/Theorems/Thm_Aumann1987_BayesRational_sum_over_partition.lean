-- Prove2me | Theorems.Thm_Aumann1987_BayesRational_sum_over_partition
-- name    : Aumann1987.BayesRational.sum_over_partition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T04:59:53.435164+00:00
-- url     : https://prove2.me/theorems/2512269d-368e-4d24-9edb-547dc21b9481
-- title:
--   Main Theorem, proof — summing over the partition gives the ex-ante inequality
-- statement:
--   Let $(\Omega,p,(\mathcal P^j),\mathbf s)$ be an information system for a game with payoffs $h$, let player $i$ be Bayes rational at every state, and let $g:\Omega\to S^i$ be constant on every element of $\mathcal P^i$. Then
--   $$
--   \sum_{\omega\in\Omega}p(\omega)\,h^i\big(\mathbf s^{-i}(\omega),g(\omega)\big)\ \le\ \sum_{\omega\in\Omega}p(\omega)\,h^i(\mathbf s(\omega)),
--   $$
--   that is, $E h^i(\mathbf s^{-i},g)\le E h^i(\mathbf s)$.
--
--   This is the law of total expectation over $\mathcal P^i$ applied to the cell-wise inequality; it turns interim rationality into the ex-ante inequality of Definition 2.1.
--
--   **Formalization Note.** The prior need not have full support; states in null cells contribute nothing to either side.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 8 (PDF p. 9), Main Theorem, proof

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

namespace Aumann1987.BayesRational

/-- **Main Theorem, proof — summing over the partition** (Aumann 1987, Econometrica 55, Sect. 3,
unnumbered step of the proof of the Main Theorem, p. 8, PDF p. 9): "multiplying both sides by
`Prob P` and summing over all `P` in `𝒫ⁱ` yields `E(hⁱ(s)) ≥ Ehⁱ(s⁻ⁱ, gⁱ)`."

In an information system `I` with common prior `p`, if player `i` is Bayes rational at every
state and `g : Ω → Sⁱ` is constant on every element of `𝒫ⁱ`, then
`Ehⁱ(s⁻ⁱ, gⁱ) ≤ Ehⁱ(s)`, the expectations being taken with respect to `p`.

**Formalization Note.** The prior need not have full support: states in cells of probability `0`
contribute nothing to either side, and Bayes rationality there is vacuous (see `condExp`). -/
theorem sum_over_partition {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type*} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S) (i : ι)
    (hrat : ∀ ω, IsBayesRationalAt h I.p I.P I.s i ω)
    (g : Ω → S i) (hg : ∀ ω ω', (I.P i).r ω ω' → g ω = g ω') :
    expPayoff h I.p (deviate I.s i g) i ≤ expPayoff h I.p I.s i := by sorry

end Aumann1987.BayesRational
