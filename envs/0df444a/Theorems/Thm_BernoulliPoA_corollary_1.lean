-- Prove2me | Theorems.Thm_BernoulliPoA_corollary_1
-- name    : BernoulliPoA.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:20.526787+00:00
-- url     : https://prove2.me/theorems/ab087444-97b0-4c4d-ac80-81fb5b3a9f55
-- title:
--   Corollary 1, p.15 (corrected: factor $Y_i$ added in (19)) — reduction to costs $c^q$
-- statement:
--   Let $\Gamma^{\mathbf p}$ be a Bernoulli congestion game with $p_i\le q$ and $0<q\le1$, and set $r_i=p_i/q\in[0,1]$. For every profile $s$, the player costs and the social cost of $\Gamma^{\mathbf p}$ equal those of the Bernoulli congestion game $\Gamma_q^{\mathbf r}$ with costs $c_e^q$ and probabilities $r_i$. Writing $Y_j\sim\mathrm{Bernoulli}(r_j)$ for independent variables and $N^Y_e(s)=\sum_jY_j\mathbb 1_{\{e\in s_j\}}$,
--   $$
--   C_i(s)=\mathsf E\Bigl[Y_i\sum_{e\in s_i}c_e^q(N_e^Y(s))\Bigr],\qquad C(s)=\mathsf E\Bigl[\sum_{e}N_e^Y(s)\,c_e^q(N_e^Y(s))\Bigr].
--   $$
--   In particular, when $p_i\equiv q$ the game $\Gamma^{\mathbf p}$ has the player costs and social cost of the deterministic atomic congestion game $\Gamma_q$ with costs $c_e^q$.
--
--   This reduction to costs $c^q$ is what the upper bound on the prophet price of anarchy runs on.
--
--   Differences from the source:
--   - correction: (19): Ci(s) = E[Σ_{e∈si} cq_e(NY_e(s))] → Ci(s) = E[Yi Σ_{e∈si} cq_e(NY_e(s))], i.e. the cost of i in Γ^r_q; reason: the printed display misses the factor Yi; for two players sharing one resource, c ≡ 1, q = 0.6, pi = 0.3, Ci = 0.3 while the printed right side is 0.45, and the corollary's sentence and (EC.6b) use the corrected form
--   - generalization: costs c : ℕ → [0,∞) nondecreasing and 0 < pi ≤ q → arbitrary real costs and 0 ≤ pi ≤ q; reason: Lemma 1 is linear in the cost, and the source's games are instances
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Corollary 1, p.15

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_expCost
import Definitions.Def_BernoulliPoA_expSocialCost
import Definitions.Def_BernoulliPoA_binomGame
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Corollary 1 (corrected (19)).** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Corollary 1, p.15: if `p_i ≤ q` and `r_i = p_i / q`, then `Γ^p` is equivalent, in player costs and social cost,
to the Bernoulli congestion game `Γ^r_q` with costs `c^q_e` and probabilities `r_i`. If `p_i ≡ q`, it is equivalent to the deterministic atomic congestion
game `Γ_q` with costs `c^q_e`.

**Formalization Note** The first clause is (19) with the factor `Y_i` that the printed display omits: `C_i(s) = E[Y_i ∑_{e ∈ s_i} c^q_e(N^Y_e(s))]`. This is the
cost `C_i` in `Γ^r_q`, as the corollary's sentence says and (EC.6b) uses. The printed (19) fails on two players sharing one resource with `c ≡ 1`, `q = 0.6`,
`p_i = 0.3`: `C_1 = 0.3`, while the printed right side is `0.45`. The second clause is (20). Costs need no sign condition, Lemma 1 being linear. -/
theorem corollary_1 {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (p : ι → ℝ) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ q) (s : ι → Finset E) :
    (∀ i, expCost G p s i = expCost (binomGame G q) (fun j => p j / q) s i) ∧
    expSocialCost G p s = expSocialCost (binomGame G q) (fun j => p j / q) s ∧
    ((∀ i, p i = q) →
      (∀ i, expCost G p s i = cost (binomGame G q) s i) ∧
      expSocialCost G p s = sumCost (binomGame G q) s) := by sorry

end BernoulliPoA
