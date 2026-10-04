-- Prove2me | Theorems.Thm_Aumann1987_BayesRational_converse
-- name    : Aumann1987.BayesRational.converse
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T05:01:02.075+00:00
-- url     : https://prove2.me/theorems/e508bac3-537c-4c7b-b487-e9cd892c8d6b
-- title:
--   Sect. 4d — every correlated equilibrium arises from a Bayes-rational information system
-- statement:
--   Let $f:\Gamma\to S$ be a correlated equilibrium on a finite probability space $(\Gamma,q)$ of a game with payoffs $h$. Then there is an information system $(\Omega,p,(\mathcal P^i),\mathbf s)$ — finite $\Omega$, common prior $p$, partitions $\mathcal P^i$, each $\mathbf s^i$ measurable with respect to $\mathcal P^i$ — in which every player is Bayes rational at every state and
--   $$
--   p\{\omega:\ \mathbf s(\omega)=a\}=q\{\gamma:\ f(\gamma)=a\}\qquad\text{for every }a\in S.
--   $$
--
--   Together with the Main Theorem this shows that, under Bayesian rationality, information systems correspond precisely to correlated equilibria.
--
--   **Formalization Note.** $\Gamma$ and the witness $\Omega$ live in `Type` (universe 0).
-- source:
--   Aumann, Correlated Equilibrium as an Expression of Bayesian Rationality, Econometrica 55 (1987), DOI 10.2307/1911154, p. 11 (PDF p. 12), Sect. 4d

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1987_BayesRational_CorrelatedEquilibrium
import Definitions.Def_Aumann1987_BayesRational_InformationSystem

namespace Aumann1987.BayesRational

/-- **Sect. 4d, the converse** (Aumann 1987, Econometrica 55, Sect. 4d, p. 11, PDF p. 12): "More
precisely, for each game `G` and each correlated equilibrium `f` of `G`, there is an information
system for which it is Bayes rational for the players to play in accordance with `s`, and the
resulting distribution is the same as that of `f`."

For every correlated equilibrium `f` on a finite probability space `(Γ, q)` there are a finite set
`Ω` and an information system `I` on `Ω` (common prior, partitions, action functions measurable
w.r.t. the partitions) in which every player is Bayes rational at every state and the distribution
of the action `n`-tuple `s` equals the distribution of `f`.

**Formalization Note.** `Γ` and the witness `Ω` live in `Type`, as in `IsCED`. -/
theorem converse {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    {Γ : Type} [Fintype Γ] (h : ι → (∀ i, S i) → ℝ) (q : Γ → ℝ) (hq : AGT.IsLottery q)
    (f : Γ → ∀ i, S i) (hf : IsCorrelatedEquilibrium h q f) :
    ∃ (Ω : Type) (_ : Fintype Ω) (I : InformationSystem Ω S),
      (∀ i ω, IsBayesRationalAt h I.p I.P I.s i ω) ∧ distr I.p I.s = distr q f := by sorry

end Aumann1987.BayesRational
