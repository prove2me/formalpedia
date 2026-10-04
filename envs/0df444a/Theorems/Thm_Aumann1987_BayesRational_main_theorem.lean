-- Prove2me | Theorems.Thm_Aumann1987_BayesRational_main_theorem
-- name    : Aumann1987.BayesRational.main_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:00:34.593204+00:00
-- url     : https://prove2.me/theorems/22eb440e-1c44-48d9-9b0f-033af0584556
-- title:
--   Main Theorem — Bayes rationality at every state yields a correlated equilibrium distribution
-- statement:
--   Let $(\Omega,p,(\mathcal P^i),\mathbf s)$ be an information system for a game with payoffs $h$: a finite set of states $\Omega$, a common prior $p$, information partitions $\mathcal P^i$, and action functions $\mathbf s^i$ measurable with respect to $\mathcal P^i$. If each player is Bayes rational at each state of the world, then the distribution of the action $n$-tuple,
--   $$
--   Q(a)=p\{\omega\in\Omega:\ \mathbf s(\omega)=a\},\qquad a\in S,
--   $$
--   is a correlated equilibrium distribution.
--
--   This is Aumann's Main Theorem: common knowledge of Bayesian rationality, under a common prior, leads to correlated equilibrium play.
--
--   **Formalization Note.** The set of states lives in `Type` (universe 0), matching the definition of a correlated equilibrium distribution.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 7 (PDF p. 8), Main Theorem

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

namespace Aumann1987.BayesRational

/-- **Main Theorem** (Aumann 1987, Econometrica 55, Sect. 3, p. 7, PDF p. 8): "If each player is
Bayes rational at each state of the world, then the distribution of the action `n`-tuple `s` is a
correlated equilibrium distribution."

For every information system `I` (finite `Ω`, common prior `p`, partitions `𝒫ⁱ`, each `sⁱ`
measurable w.r.t. `𝒫ⁱ`) in which every player is Bayes rational at every state, the distribution
`a ↦ p{ω : s(ω) = a}` of `s` is a correlated equilibrium distribution of the game.

**Formalization Note.** `Ω` lives in `Type` (universe 0), matching `IsCED`, whose witnessing
probability space ranges over `Type`; every finite set is in bijection with some `Fin n`, so
nothing is lost. -/
theorem main_theorem {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S)
    (hrat : ∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) :
    IsCED h (distr I.p I.s) := by sorry

end Aumann1987.BayesRational
