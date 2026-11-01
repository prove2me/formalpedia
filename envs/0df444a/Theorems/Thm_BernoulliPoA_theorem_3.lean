-- Prove2me | Theorems.Thm_BernoulliPoA_theorem_3
-- name    : BernoulliPoA.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:54.675493+00:00
-- url     : https://prove2.me/theorems/04b24155-ec17-4084-a739-f77ed0f78312
-- title:
--   Theorem 3, p.20 — $\mathsf{PPoA}(\mathcal C,q)=\gamma_{\mathsf{pr}}(\mathcal C,q)$
-- statement:
--   For each family $\mathcal C$ of nonnegative and nondecreasing cost functions and each $q\in(0,1]$,
--   $$
--   \mathsf{PPoA}(\mathcal C,q)=\gamma_{\mathsf{pr}}(\mathcal C,q).
--   $$
--   Here $\mathsf{PPoA}(\mathcal C,q)$ is the supremum of the prophet price of anarchy over all Bernoulli congestion games with costs in $\mathcal C$ and participation probabilities $0<p_i\le q$, for any numbers of players and resources, and $\gamma_{\mathsf{pr}}(\mathcal C,q)$ is the infimum of $\lambda/(1-\mu)$ over the pairs satisfying $(\lambda,\mu,q)$-smoothness.
--
--   The equality holds in $[0,\infty]$. By taking $q=1$ the paper recovers the tight bound $\mathsf{PoA}(\mathcal C)=\gamma(\mathcal C)$ of Roughgarden (2015) for deterministic congestion games.
--
--   Differences from the source:
--   - reading: (26) fixes no value for C(s)/C_pr when both vanish, while (6) sets PoA := 1 for deterministic games → ratio in ℝ≥0∞, with x/0 = ⊤ for x > 0 and 0/0 = 0; reason: x/0 = ⊤ is the value used in Case 1 (p.ec3); with 0/0 := 1 the theorem fails for C ⊆ {c₀}, where γ_pr = 0, and the two conventions give the same supremum as soon as C has a function nonzero at a positive load
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set is nonempty in G(C,q); reason: a game without a strategy for some player has no profile; this only excludes undefined cases
--   - encoding: players {1,…,n}, finite resource set E, and a supremum over all games → players Fin n, resources Fin r, supremum over n, r ∈ ℕ in ℝ≥0∞; reason: Lean indexing of the same class of games; both sides may be +∞
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Theorem 3, p.20

import Mathlib
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_worstPPoA
import Definitions.Def_BernoulliPoA_gammaPr

namespace BernoulliPoA

/-- **Theorem 3.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Theorem 3, p.20: for each family `C` of nonnegative and nondecreasing cost functions and each `q ∈ (0, 1]`, `PPoA(C, q) = γ_pr(C, q)`.

**Formalization Note** The equality is in `ℝ≥0∞`, both sides possibly `⊤`. `PPoA(Γ^p)` divides in `ℝ≥0∞`, with `x / 0 = ⊤` for `x > 0` and `0 / 0 = 0`; the second value is the reading under which the theorem holds
for every `C`, including the classes whose functions all vanish at positive loads (`C = ∅`, `C = {c₀}`), where both sides are `0`. Under the paper's convention (6) for deterministic games, `PoA := 1` when
the optimum is `0`, the theorem would fail for those classes, and the two conventions agree as soon as `C` has a function nonzero at a positive load. Cost functions are constrained at loads `≥ 1` only. -/
theorem theorem_3 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    worstPPoA C q = gammaPr C q := by sorry

end BernoulliPoA
