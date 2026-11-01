-- Prove2me | Theorems.Thm_BernoulliPoA_proposition_2
-- name    : BernoulliPoA.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:29.235862+00:00
-- url     : https://prove2.me/theorems/5e15753b-7638-46e3-9436-29513ffa17a8
-- title:
--   Proposition 2, p.20 — $\mathsf{PPoA}(\Gamma^{\mathbf p})\le\gamma_{\mathsf{pr}}(\mathcal C,q)$
-- statement:
--   For each family $\mathcal C$ of nonnegative nondecreasing costs, each $q\in(0,1]$ and each Bernoulli congestion game $\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)$,
--   $$
--   \mathsf{PPoA}(\Gamma^{\mathbf p})\le\gamma_{\mathsf{pr}}(\mathcal C,q).
--   $$
--
--   This is the upper bound of the goal theorem.
--
--   Differences from the source:
--   - reading: (26) fixes no value for C(s)/C_pr when both vanish, while (6) sets PoA := 1 for deterministic games → ratio in ℝ≥0∞, with x/0 = ⊤ for x > 0 and 0/0 = 0; reason: x/0 = ⊤ is the value used in Case 1 (p.ec3); with 0/0 := 1 the theorem fails for C ⊆ {c₀}, where γ_pr = 0, and the two conventions give the same supremum as soon as C has a function nonzero at a positive load
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set is nonempty in G(C,q); reason: a game without a strategy for some player has no profile; this only excludes undefined cases
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Proposition 2, p.20

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_PPoA
import Definitions.Def_BernoulliPoA_InClassQ
import Definitions.Def_BernoulliPoA_gammaPr
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Proposition 2.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Proposition 2, p.20: for each Bernoulli congestion game `Γ^p ∈ G(C, q)`, `PPoA(Γ^p) ≤ γ_pr(C, q)`. -/
theorem proposition_2 {n r : ℕ} {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (G : CongestionGame (Fin n) (Fin r)) (p : Fin n → ℝ) (hG : InClassQ C q G p) :
    PPoA G p ≤ gammaPr C q := by sorry

end BernoulliPoA
