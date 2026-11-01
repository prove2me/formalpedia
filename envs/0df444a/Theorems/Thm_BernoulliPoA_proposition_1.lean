-- Prove2me | Theorems.Thm_BernoulliPoA_proposition_1
-- name    : BernoulliPoA.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:52.223876+00:00
-- url     : https://prove2.me/theorems/2f1f8549-967f-4f19-90e3-7d9c1f813e33
-- title:
--   Proposition 1, p.13 — every BCG is an exact potential game and has a Bayes-Nash equilibrium
-- statement:
--   Let $\Gamma^{\mathbf p}$ be a Bernoulli congestion game with nonempty strategy sets. For each strategy profile $s$ and each unilateral deviation $s'=(s_i',s_{-i})$ of a player $i$,
--   $$
--   C_i(s')-C_i(s)=\Phi(s')-\Phi(s),
--   $$
--   where $\Phi$ is the expected Rosenthal potential. In particular the set $\mathrm{NE}(\Gamma^{\mathbf p})$ of Bayes-Nash equilibria is nonempty.
--
--   This makes the maximum defining the prophet price of anarchy a maximum over a nonempty set.
--
--   Differences from the source:
--   - generalization: costs ce : ℕ → [0,∞) nondecreasing and pi ∈ (0,1] → arbitrary real costs and pi ∈ [0,1]; reason: the identity uses no sign or monotonicity, and the source's games are instances
--   - generalization: every BCG is an exact potential game, i.e. some Φ satisfies (15) → (15) holds for the explicit potential Φ of (16); reason: the paper's proof exhibits this Φ, and the existence claim follows at once
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set is nonempty (hypothesis hne); reason: a game without a strategy for some player has no profile; this only excludes undefined cases
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Proposition 1, p.13, with (15), p.13, and (16), p.14

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_expCost
import Definitions.Def_BernoulliPoA_expPotential
import Definitions.Def_BernoulliPoA_IsBNE
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Proposition 1.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Proposition 1, p.13, with (15), p.13, and (16), p.14: every Bernoulli congestion game is an exact potential game,
with the expected Rosenthal potential `Φ` of (16), and `NE(Γ^p)` is nonempty.

**Formalization Note** The first clause is (15) for each profile `s` and each unilateral deviation. Costs are arbitrary reals, since
the identity uses neither their sign nor their monotonicity, and `p_i ∈ [0,1]` covers the paper's `p_i ∈ (0,1]`. -/
theorem proposition_1 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (p : ι → ℝ) (hne : ∀ i, (G.strategies i).Nonempty)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    (∀ s, IsProfile G s → ∀ i, ∀ S ∈ G.strategies i,
      expCost G p (Function.update s i S) i - expCost G p s i =
        expPotential G p (Function.update s i S) - expPotential G p s) ∧
    ∃ s, IsBNE G p s := by sorry

end BernoulliPoA
