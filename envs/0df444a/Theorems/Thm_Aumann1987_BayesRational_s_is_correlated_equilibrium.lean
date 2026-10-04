-- Prove2me | Theorems.Thm_Aumann1987_BayesRational_s_is_correlated_equilibrium
-- name    : Aumann1987.BayesRational.s_is_correlated_equilibrium
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:00:19.917468+00:00
-- url     : https://prove2.me/theorems/a5b320bd-a5b3-43c3-8d49-b769c1e46ef3
-- title:
--   Main Theorem, proof — the action n-tuple s is a correlated equilibrium on (Ω, p)
-- statement:
--   Let $(\Omega,p,(\mathcal P^i),\mathbf s)$ be an information system — finite $\Omega$, common prior $p$, partitions $\mathcal P^i$, each $\mathbf s^i$ constant on the elements of $\mathcal P^i$ — for a game with payoffs $h$. If every player is Bayes rational at every state, then $\mathbf s:\Omega\to S$, viewed as a correlated strategy $n$-tuple on the probability space $(\Omega,p)$, is a correlated equilibrium: for every player $i$ and every $\varphi:S^i\to S^i$,
--   $$
--   E h^i(\mathbf s)\ \ge\ E h^i\big(\mathbf s^{-i},\varphi\circ\mathbf s^i\big).
--   $$
--
--   This is the heart of the Main Theorem: the information system itself serves as the probability space of a correlated equilibrium.
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, pp. 7-8 (PDF pp. 8-9), Main Theorem, proof

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

namespace Aumann1987.BayesRational

/-- **Main Theorem, proof — `s` is a correlated equilibrium on `(Ω, p)`** (Aumann 1987,
Econometrica 55, Sect. 3, unnumbered step of the proof of the Main Theorem, pp. 7–8, PDF pp. 8–9):
"Indeed, if we set `Γ := (Ω, p)`, then `s` itself is such a function. … For `f = s`, this is
precisely the condition (2.2) that defines correlated equilibrium."

In an information system `I` (finite `Ω`, common prior `p`, partitions `𝒫ⁱ`, each `sⁱ`
measurable w.r.t. `𝒫ⁱ`), if every player is Bayes rational at every state, then the action
`n`-tuple `s`, viewed as a correlated strategy `n`-tuple on the probability space `(Ω, p)`, is a
correlated equilibrium in the sense of Definition 2.1.

**Formalization Note.** Measurability of each `sⁱ` is the field `I.measurable`; it is what makes
every deviation `φ ∘ sⁱ` constant on the cells of `𝒫ⁱ`. -/
theorem s_is_correlated_equilibrium {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Ω : Type*} [Fintype Ω] (h : ι → (∀ i, S i) → ℝ) (I : InformationSystem Ω S)
    (hrat : ∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) :
    IsCorrelatedEquilibrium h I.p I.s := by sorry

end Aumann1987.BayesRational
