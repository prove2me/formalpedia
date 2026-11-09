-- Prove2me | Theorems.Thm_BosonicLearn_proposition_5
-- name    : BosonicLearn.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:37:47.8292+00:00
-- url     : https://prove2.me/theorems/000a67b7-28b4-4629-a21e-079fe65ac272
-- title:
--   Proposition 5 — with $N=o(n/(\nu^2\xi^2))$ copies, $\Pr(\|\mathcal A(x)-X_0\|_{\mathrm{tr}}\le na/2)\le0.1+o(1)$
-- statement:
--   Let $X_0\sim\mu$ (the prior (32)), let an adaptive single-copy scheme measure $N$ copies of $\rho_{R_{X_0}}$ with transcript $x\sim\mathcal T_{X_0}$, and let $\mathcal A$ be a possibly randomized algorithm mapping transcripts to $\mathrm{Herm}_0(n)$. If $N=o(n/(\nu^2\xi^2))$, then
--
--   $$\Pr_{\mathcal A,\ X_0\sim\mu,\ x\sim\mathcal T_{X_0}}\big(\|\mathcal A(x)-X_0\|_{\mathrm{tr}}\le na/2\big)\le0.1+o(1).$$
--
--   Precisely: there are $\xi_0\in(0,1/32)$ and $a_0>0$ such that for all $a\in(0,a_0]$ and $\eta>0$ there are $\kappa>0$ and $n_1$ with the probability at most $0.1+\eta$ whenever $n\ge n_1$, $\nu\in[1/n,1]$, $\xi\in(0,\xi_0]$ and $N\nu^2\xi^2\le\kappa n$, for every scheme and every algorithm.
--
--   With Lemma 12 it turns a learner of $\rho_{R_X}$ into an estimator of $X$ and gives Theorem 5.
--
--   Differences from the source:
--   - reading: N = o(n/(ν²ξ²)) ⇒ Pr ≤ 0.1 + o(1) → ∀ η > 0 ∃ κ > 0 ∃ n₁ ∀ n ≥ n₁ ∀ ν ξ N with Nν²ξ² ≤ κn: Pr ≤ 0.1 + η; reason: uniform reading of both o(·), equivalent to the sequential one
--   - reading: a the small constant of Proposition 1 → ∃ a₀ > 0 and the claim for every a ∈ (0, a₀]; reason: the event shrinks with a, so this is equivalent to the claim for the chosen a
--   - encoding: "single-copy measurements", possibly adaptive, with an estimator → adaptive schemes of POVMs with an arbitrary measurable outcome space, round laws measurable in the earlier outcomes, and a Markov-kernel estimator to density operators; reason: the paper's model (§1.1 p. 5, §4 p. 19, §5.1 p. 30); measurability makes the transcript a random variable
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Proposition 5, Eq. (96), p. 39

import Mathlib
import Definitions.Def_BosonicLearn_transcriptLaw
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_priorMu
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Proposition 5 (Hardness of learning `X₀`).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Proposition 5, Eq. (96), p. 39: "Let {ρ_{R_{X_0}} : X_0 ∈ G_supp} be the family of passive Gaussian states as
defined before, with the prior distribution X_0 ∼ µ. Let A denote a (possibly randomized) algorithm that takes as
input the transcript of outcomes x and outputs an estimator A(x) ∈ Herm_0(n) for X_0. Given that N = o(n/(ν²ξ²)),
one must have Pr_{A, X_0∼µ, x∼T_{X_0}}(‖A(x) − X_0‖_tr ≤ na/2) ≤ 0.1 + o(1)."
Setting (§5.1): `1/n ≤ ν ≤ 1`, `ξ` small, `a` the small constant of Proposition 1; `T_{X_0}` is the transcript law of
a fixed adaptive single-copy scheme on `ρ_{R_{X_0}}`.

There are `ξ₀ ∈ (0, 1/32)` and `a₀ > 0` such that for every `a ∈ (0, a₀]` and `η > 0` there are `κ > 0` and `n₁`
with: for all `n ≥ n₁`, `ν ∈ [1/n, 1]`, `ξ ∈ (0, ξ₀]`, every `N` with `Nν²ξ² ≤ κn`, every adaptive single-copy scheme
on `N` copies (any outcome space) and every Markov kernel `A` from transcripts to `Herm₀(n)`,
`Pr_{X₀∼µ, x∼T_{X₀}, A}(‖A(x) − X₀‖_tr ≤ na/2) ≤ 0.1 + η`.

**Formalization Note.** Both `o(·)` are read uniformly (`∀η ∃κ ∃n₁`), which is equivalent to the sequential reading.
"For all `a ≤ a₀`" is equivalent to "for some `a`" since the event shrinks with `a`. -/
theorem proposition_5 :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a ≤ a₀ →
      ∀ η : ℝ, 0 < η → ∃ κ : ℝ, 0 < κ ∧ ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
        ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ →
        ∀ N : ℕ, (N : ℝ) * ν ^ 2 * ξ ^ 2 ≤ κ * n →
        ∀ (O : Type) [MeasurableSpace O] (S : AdaptiveScheme n N O) (A : Kernel (Fin N → O) (Herm0 n)),
          IsMarkovKernel A →
          ∫⁻ X₀, ∫⁻ x, A x {Y | WHMultiplicativity.schattenNorm 1 ((Y - X₀ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) ≤ n * a / 2}
              ∂(transcriptLaw S (fugacityCoeff (fugacityFamily ν ξ X₀))) ∂(priorMu n)
            ≤ ENNReal.ofReal (1 / 10 + η) := by sorry

end BosonicLearn
