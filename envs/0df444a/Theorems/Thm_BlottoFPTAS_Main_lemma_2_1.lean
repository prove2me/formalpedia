-- Prove2me | Theorems.Thm_BlottoFPTAS_Main_lemma_2_1
-- name    : BlottoFPTAS.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T00:40:53.095647+00:00
-- url     : https://prove2.me/theorems/6fa110bd-f6cb-4d62-a7e3-2a3e07aa441f
-- title:
--   Lemma 2.1 — payoffs and regrets are Lipschitz in the marginal-CDF distance d
-- statement:
--   Let $v_i>0$ with $\sum_iv_i=1$ and $d(\mu,\nu)=\max_i\sup_t|F_{\mu,i}(t)-F_{\nu,i}(t)|$. (i) For any fixed strategy $\rho$ of one player, replacing the opponent's strategy $\mu$ by $\nu$ changes the expected payoff (of either player, with the fixed strategy in either role) by at most $d(\mu,\nu)$. (ii) If $d(\mu_A,\mu'_A)\le\delta_A$ and $d(\mu_B,\mu'_B)\le\delta_B$, then
--   $$\mathrm{Reg}_A(\mu'_A,\mu'_B)\le\mathrm{Reg}_A(\mu_A,\mu_B)+\delta_A+2\delta_B,\qquad \mathrm{Reg}_B(\mu'_A,\mu'_B)\le\mathrm{Reg}_B(\mu_A,\mu_B)+\delta_B+2\delta_A.$$
--   Payoffs depend only on marginals, and this lemma converts CDF errors (rounding, finite shifts, midpoint uniforms) into regret errors throughout §5 and Appendix F.
--
--   **Formalization Note.** A pure strategy is its point mass.
--
--   Differences from the source:
--   - generalization: the fixed strategy and the two strategy profiles are feasible strategies (on X(1), X(b)) → arbitrary Borel probability measures on Fin n → ℝ, and any real b in the regret of B; reason: the proof uses only the marginal CDFs; feasible strategies are the special case
--   - reading: replacing the opponent's strategy changes the expected payoff by at most d(μ, ν) → four inequalities: A's and B's expected payoff, with the changed strategy in either player's role; reason: the sentence covers either player; constant-sum makes the four equivalent in pairs
--   - encoding: mixed strategy = probability distribution on the pure strategy space → Borel probability measure on Fin n → ℝ with full mass on X(c); reason: Lean convention; same strategies
-- source:
--   Bichler, Ghosh, Efficient Equilibrium Computation in Colonel Blotto Games, arXiv:2611.05221 (held version, sha256 cac3638e…), p. 6, Lemma 2.1

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_Game

open MeasureTheory

namespace BlottoFPTAS.Main

/-- **Lemma 2.1** (Bichler, Ghosh, arXiv:2611.05221, held version sha256 cac3638e…, p. 6).
For values `v_i > 0` summing to one: (i) for any fixed strategy `ρ` of one player (a pure strategy
is a point mass), replacing the opponent's strategy `μ` by `ν` changes either player's expected
payoff by at most `d(μ, ν)`, in either role; (ii) if `d(μ_A, μ'_A) ≤ δ_A` and `d(μ_B, μ'_B) ≤ δ_B`
then `Reg_A(μ'_A, μ'_B) ≤ Reg_A(μ_A, μ_B) + δ_A + 2δ_B` and
`Reg_B(μ'_A, μ'_B) ≤ Reg_B(μ_A, μ_B) + δ_B + 2δ_A`. -/
theorem lemma_2_1 {n : ℕ} (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : ∀ i, 0 < v i)
    (hsum : ∑ i, v i = 1) :
    (∀ ρ μ ν : Measure (Fin n → ℝ), IsProbabilityMeasure ρ → IsProbabilityMeasure μ →
        IsProbabilityMeasure ν →
        |expUA v ρ μ - expUA v ρ ν| ≤ cdfDist μ ν ∧
        |expUB v ρ μ - expUB v ρ ν| ≤ cdfDist μ ν ∧
        |expUA v μ ρ - expUA v ν ρ| ≤ cdfDist μ ν ∧
        |expUB v μ ρ - expUB v ν ρ| ≤ cdfDist μ ν) ∧
    (∀ (b : ℝ) (μA μB μA' μB' : Measure (Fin n → ℝ)) (δA δB : ℝ),
        IsProbabilityMeasure μA → IsProbabilityMeasure μB →
        IsProbabilityMeasure μA' → IsProbabilityMeasure μB' →
        cdfDist μA μA' ≤ δA → cdfDist μB μB' ≤ δB →
        regA v μA' μB' ≤ regA v μA μB + δA + 2 * δB ∧
        regB v b μA' μB' ≤ regB v b μA μB + δB + 2 * δA) := by sorry

end BlottoFPTAS.Main
