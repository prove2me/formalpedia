-- Prove2me | Theorems.Thm_BunkbedAux_probOf_mem_unitInterval
-- name    : BunkbedAux.probOf_mem_unitInterval
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T03:46:44.235323+00:00
-- url     : https://prove2.me/theorems/6d7cca75-b060-4147-a859-04550e6379d0
-- title:
--   Percolation probabilities lie in $[0,1]$
-- statement:
--   In this development a percolation probability is defined combinatorially, as
--   $$\mathbb{P}[\mathcal{E}] \;=\; \sum_{S \subseteq E} \mathbf{1}[\mathcal{E}(S)]\,\mathrm{wt}(S), \qquad \mathrm{wt}(S) \;=\; \prod_{e \in S} w(e)\prod_{e \in E \setminus S}\bigl(1 - w(e)\bigr),$$
--   with no constraint imposed on the weight function $w$. In particular the definition makes sense for arbitrary $w : \mathrm{Sym}^2(V) \to \mathbb{Q}$, and for such $w$ the resulting quantity need not lie in $[0,1]$ — or even be nonnegative.
--
--   This lemma records that as soon as $w$ is a genuine assignment of probabilities, $0 \le w(e) \le 1$ for every edge, the quantity $\mathbb{P}[\mathcal{E}]$ is a genuine probability:
--   $$0 \;\le\; \mathbb{P}[\mathcal{E}] \;\le\; 1$$
--   for every decidable event $\mathcal{E}$.
--
--   The lower bound holds because each configuration weight is a product of nonnegative factors. The upper bound holds because the weights sum to $1$ over all configurations — the total-mass identity, which is itself valid for arbitrary $w$ — and because dropping the indicator can only increase a sum of nonnegative terms.
--
--   **Mathematical role.** This is the basic sanity fact needed whenever a percolation probability is fed into an argument that expects a probability distribution. For instance, the five partition probabilities of a hyperedge gadget are used as the state distribution of a Wierman--Ziff model; that requires them to be nonnegative and to sum to one, and the nonnegativity is exactly this lemma. It is stated for an arbitrary finite vertex type and arbitrary event, so it applies uniformly.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 2 (p. 2), where Bernoulli bond percolation and its connection probabilities are set up.

import Definitions.Def_BunkbedPercolation
open Bunkbed Finset

namespace BunkbedAux

/-- **Percolation probabilities lie in `[0,1]`.** If every edge weight is a genuine probability
then so is the probability of any event. -/
theorem probOf_mem_unitInterval {V : Type*} [Fintype V] [DecidableEq V] (E : Finset (Sym2 V))
    (w : Sym2 V → ℚ) (hw0 : ∀ e, 0 ≤ w e) (hw1 : ∀ e, w e ≤ 1)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    0 ≤ probOf E w ev ∧ probOf E w ev ≤ 1 := by
  sorry

end BunkbedAux
