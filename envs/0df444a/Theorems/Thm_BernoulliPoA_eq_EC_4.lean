-- Prove2me | Theorems.Thm_BernoulliPoA_eq_EC_4
-- name    : BernoulliPoA.eq_EC_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:44:13.764214+00:00
-- url     : https://prove2.me/theorems/e337f8f6-9c3c-44ee-bdc1-4b17a3d914df
-- title:
--   Proof of Proposition 2, (EC.4)–(EC.5), pp.ec1–ec2 — the prophet-like deviation bound
-- statement:
--   Let $\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)$ and let $(\lambda,\mu)$ satisfy (28). For every strategy profile $s$ and every family $(s^{\mathcal I})_{\mathcal I\subseteq\mathcal N}$ of strategy profiles,
--   $$
--   \sum_{i\in\mathcal N}\sum_{\mathcal I\ni i}\frac{p(\mathcal I)}{p_i}\,C_i\bigl(s_i^{\mathcal I},s_{-i}\bigr)\le\lambda\sum_{\mathcal I}p(\mathcal I)\sum_ en_e^{\mathcal I}(s^{\mathcal I})\,c_e\bigl(n_e^{\mathcal I}(s^{\mathcal I})\bigr)+\mu\,C(s).
--   $$
--   When each $s^{\mathcal I}$ solves the prophet's problem, the first term on the right is $\lambda\,C_{\mathsf{pr}}$, and the left side is the expected cost of the prophet-like deviations.
--
--   This is the inequality from which the upper bound on the prophet price of anarchy is drawn at equilibrium.
--
--   Differences from the source:
--   - generalization: s^I a prophet optimal profile for each I → any family of strategy profiles (s^I)_I; reason: (28) is applied at k = n^I_e(s^I) whatever s^I is; the prophet's minimizers are an instance
--   - encoding: expected deviation cost under the mixed prophet-like strategies σ*_i → the sum R of (EC.5) with P(s*_i = s^I_i) = p(I)/p_i written out; reason: (EC.5) is the source's own expression of the left side
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set is nonempty in G(C,q); reason: a game without a strategy for some player has no profile; this only excludes undefined cases
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Proposition 2, displays (EC.4) and (EC.5), pp.ec1–ec2

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_weight
import Definitions.Def_BernoulliPoA_restrict
import Definitions.Def_BernoulliPoA_expCost
import Definitions.Def_BernoulliPoA_expSocialCost
import Definitions.Def_BernoulliPoA_InClassQ
import Definitions.Def_BernoulliPoA_prophetSmoothParams
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **The prophet-like deviation bound (EC.4), in the form (EC.5).** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Proposition 2, displays (EC.4) and (EC.5), pp.ec1–ec2: for `(λ, μ)` satisfying (28),
any strategy profile `s` and the prophet's profiles `(s^I)_I`,
`∑_i ∑_{I ∋ i} (p(I) / p_i) C_i(s^I_i, s_{-i}) ≤ λ C_pr + μ C(s)`.

**Formalization Note** The left side is `R` of (EC.5), i.e. the expected deviation cost of the prophet-like strategies with the mixed strategies written out, and
`∑_I p(I) ∑_e n^I_e(s^I) c_e(n^I_e(s^I))` is `C_pr` of (25) when `s^I` solves (24). The statement holds for every family `(s^I)_I` of profiles, optimal or not, as (28)
is applied at `k = n^I_e(s^I)` whatever `s^I` is; the paper's case is the family of minimizers. -/
theorem eq_EC_4 {n r : ℕ} {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (G : CongestionGame (Fin n) (Fin r)) (p : Fin n → ℝ) (hG : InClassQ C q G p)
    {lam mu : ℝ} (hx : (lam, mu) ∈ prophetSmoothParams C q)
    (s : Fin n → Finset (Fin r)) (hs : IsProfile G s)
    (sI : Finset (Fin n) → Fin n → Finset (Fin r)) (hsI : ∀ I, IsProfile G (sI I)) :
    ∑ i, ∑ I ∈ Finset.univ.filter (fun I : Finset (Fin n) => i ∈ I),
        (weight p I / p i) * expCost G p (Function.update s i (sI I i)) i ≤
      lam * ∑ I : Finset (Fin n), weight p I * sumCost G (restrict (sI I) I) +
        mu * expSocialCost G p s := by sorry

end BernoulliPoA
