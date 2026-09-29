-- Prove2me | Theorems.Thm_AGT_nash_existence
-- name    : AGT.nash_existence
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:15.136727+00:00
-- url     : https://prove2.me/theorems/28dd41e8-3eaf-476e-bea7-bd6793f53d2c
-- title:
--   Every finite game has a mixed Nash equilibrium
-- statement:
--   Every game with a finite set of players and finite, nonempty strategy sets has a Nash equilibrium of mixed strategies — Nash's 1951 theorem, stated as Theorem 1.8 of *Algorithmic Game Theory*, and the goal of this mission. Formally: for every finite family $(S_i)_{i \in \iota}$ of finite nonempty strategy types and every payoff assignment $u_i : \prod_j S_j \to \mathbb{R}$, there is a mixed profile $\sigma = (\sigma_i)_i$ — each $\sigma_i$ a lottery on $S_i$, players randomizing independently — such that for every player $i$ and every lottery $\tau$ on $S_i$,
--   $$U_i(\sigma_{-i}, \tau) \;\le\; U_i(\sigma),$$
--   where $U_i$ is the expected payoff under the product distribution.
--
--   *A note on the hypotheses.* Both finiteness assumptions are load-bearing, as §1.3.5 of the book stresses: with infinitely many players, or with infinite strategy sets (the pricing game, Example 1.9), equilibria can fail to exist. Nonemptiness of each $S_i$ is likewise necessary — an empty strategy set admits no lottery at all. The player set itself may be empty, in which case the empty profile is vacuously an equilibrium. Deviations range over all mixed strategies, not only pure ones; the equivalence of the two conditions is a lemma a solution will likely prove along the way.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 1.3.4, Theorem 1.8, p. 12

import Definitions.Def_agt_games

namespace AGT

/-- **Theorem 1.8 of *Algorithmic Game Theory* (Nash, 1951)**, the capstone
of Chapter 1: any game with a finite set of players and finite strategy sets
has a Nash equilibrium of mixed strategies.

Both finiteness hypotheses are essential, as the book stresses in §1.3.5:
with infinitely many players, or with infinite strategy sets (the pricing
game, Example 1.9), a mixed Nash equilibrium can fail to exist.  The
nonemptiness of the strategy sets is likewise necessary — with an empty
strategy set there are no lotteries at all.  `Nonempty ι` is not required:
in the playerless game the empty profile is (vacuously) an equilibrium. -/
theorem nash_existence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∃ σ : ∀ i, S i → ℝ, IsMixedNash u σ := by
  sorry

end AGT
