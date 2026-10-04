-- Prove2me | Theorems.Thm_Aumann1987_BayesRational_ced_iff_bayes_rational_system
-- name    : Aumann1987.BayesRational.ced_iff_bayes_rational_system
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:01:13.994913+00:00
-- url     : https://prove2.me/theorems/7a0c650e-6e51-4ba5-b943-aa4517f5b3e4
-- title:
--   Main Theorem and converse — c.e.d.s are exactly the action distributions of Bayes-rational information systems
-- statement:
--   Let $G$ be an $n$-person game with action sets $S^i$ and payoffs $h^i$, and let $Q$ be a real function on action $n$-tuples $S=S^1\times\dots\times S^n$. Then $Q$ is a correlated equilibrium distribution of $G$ if and only if there is an information system — a finite set $\Omega$ of states, a common prior $p$ on $\Omega$, an information partition $\mathcal P^i$ of $\Omega$ for each player, and action functions $\mathbf s^i:\Omega\to S^i$ measurable with respect to $\mathcal P^i$ — in which every player is Bayes rational at every state and
--   $$
--   Q(a)=p\{\omega\in\Omega:\ \mathbf s(\omega)=a\}\qquad\text{for every }a\in S.
--   $$
--
--   This is the two-sided form announced in the paper's introduction: if each player maximizes expected utility given his information at every state, under a common prior, the chosen actions form a correlated equilibrium, and conversely every correlated equilibrium arises in this way.
--
--   **Formalization Note.** State spaces and probability spaces range over `Type` (universe 0), which loses nothing for finite sets. Bayes rationality at a state whose information cell has probability $0$ is vacuous ($0/0=0$ in Lean); the prior need not have full support.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 7 (PDF p. 8), Main Theorem, and p. 11 (PDF p. 12), Sect. 4d; announced p. 2 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

namespace Aumann1987.BayesRational

/-- **Main Theorem and its converse** (Aumann 1987, Econometrica 55, Main Theorem, Sect. 3, p. 7,
PDF p. 8, and its converse, Sect. 4d, p. 11, PDF p. 12; announced in Sect. 1, p. 2, PDF p. 3):
"Thus under Bayesian rationality, the set of all information systems corresponds precisely to the
set of all correlated equilibria."

A function `Q` on action `n`-tuples is a correlated equilibrium distribution of the game with
payoffs `h` if and only if there is an information system — a finite set `Ω` of states, a common
prior `p` on `Ω`, an information partition `𝒫ⁱ` for each player, and action functions `sⁱ`
measurable w.r.t. `𝒫ⁱ` — in which every player is Bayes rational at every state and the
distribution of the action `n`-tuple `s` is `Q`.

**Formalization Note.** Finite sets of states and finite probability spaces range over `Type`
(universe 0), which loses nothing for finite sets. Bayes rationality at a state whose cell has
probability `0` is vacuous (`condExp` divides by `0` and returns `0`); the paper's argument
never uses such states. The prior is not required to have full support. -/
theorem ced_iff_bayes_rational_system {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (h : ι → (∀ i, S i) → ℝ) (Q : (∀ i, S i) → ℝ) :
    IsCED h Q ↔
      ∃ (Ω : Type) (_ : Fintype Ω) (I : InformationSystem Ω S),
        (∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) ∧ distr I.p I.s = Q := by sorry

end Aumann1987.BayesRational
