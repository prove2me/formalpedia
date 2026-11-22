-- Prove2me | Theorems.Thm_AgnGaussTomo_Supplement_theorem_5_6
-- name    : AgnGaussTomo.Supplement.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:02:54.40927+00:00
-- url     : https://prove2.me/theorems/7c3f8d5b-ef6e-43d1-b6ff-ad685cc5125c
-- title:
--   Theorem 5.6 — Gaussian measurements need $N\ge\eta^{-1}\exp(\Omega(n^{1/3}))$ copies to reach infidelity $\mathrm{opt}+c\eta^2$
-- statement:
--   There are universal constants $c>0$, $C>0$, $c'>0$ and $n_0$ such that for every $n\ge n_0$ and every $\eta\in(0,1/4]$ there exist two $(n+1)$-mode states $\rho_+,\rho_-$ (density operators on the Fock space of $n+1$ modes) with the following properties.
--
--   1. $\mathrm{opt}_+=\mathrm{opt}_-\le C\eta$, where $\mathrm{opt}_\pm=\inf_{|\psi\rangle\in\mathcal G}d_{\mathrm{IF}}(\rho_\pm,|\psi\rangle\langle\psi|)$ is the smallest infidelity $d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)=1-\langle\psi|\rho|\psi\rangle$ with a pure Gaussian state.
--   2. $d_{\mathrm{tr}}(\rho_\pm,|0\rangle\langle0|^{\otimes(n+1)})\le\eta$: both states are $\eta$-close in trace distance to the vacuum.
--   3. Let an algorithm use only Gaussian measurements on $N$ copies and output a pure state $|\hat\psi\rangle$. If its output satisfies $d_{\mathrm{IF}}(\rho_+,|\hat\psi\rangle\langle\hat\psi|)\le\mathrm{opt}_++c\eta^2$ with probability at least $2/3$ when it is run on copies of $\rho_+$, and $d_{\mathrm{IF}}(\rho_-,|\hat\psi\rangle\langle\hat\psi|)\le\mathrm{opt}_-+c\eta^2$ with probability at least $2/3$ when it is run on copies of $\rho_-$, then
--
--   $$
--   N\ge\eta^{-1}\exp\big(c'\,n^{1/3}\big).
--   $$
--
--   An algorithm that uses only Gaussian measurements on $N$ copies is a **Gaussian protocol**: one measurement of $\rho^{\otimes N}$ with outcomes $(y,u)\in\mathbb R^{2N(n+1)}\times\mathbb R$, where $u$ is a uniform random number in $[0,1]$ and the effect density at $(y,u)$ is $(2\pi)^{-N(n+1)}D(y)\,\tau(y,u)\,D(y)^\dagger$ with a mean-zero Gaussian seed state $\tau(y,u)$ that may depend on the outcome, followed by an arbitrary function from outcomes to pure states. This covers adaptive sequences of single-copy Gaussian measurements, joint Gaussian measurements of several or all copies, adaptive Gaussian feed-forward, and classical randomness and processing.
--
--   This is the negative half of the paper's separation: Gaussian measurements, which reach $O(\mathrm{opt})+\epsilon$ (Theorem 5.1), need exponentially many copies in $n^{1/3}$ to reach the strong agnostic guarantee $\mathrm{opt}+\epsilon$ that non-Gaussian measurements achieve with $\widetilde O(n^2)$ copies (Theorem 3.8).
--
--   **Formalization Note** The states $\rho_\pm$ are existentially quantified and may depend on $n$ and $\eta$; the constants may not. The outputs are arbitrary pure states, not necessarily Gaussian.
--
--   Differences from the source:
--   - reading: universal constant c > 0, sufficiently large n, opt₊ = opt₋ = O(η), N ≥ η^{-1} exp(Ω(n^{1/3})) → ∃ c > 0, C > 0, c′ > 0 and n₀, chosen before n and η, with opt± ≤ C·η and N ≥ η^{-1}·exp(c′·n^{1/3}) for all n ≥ n₀ and η ∈ (0, 1/4]; reason: O and Ω hide absolute constants and "sufficiently large n" is a threshold n₀ independent of η; a multiplicative constant in front of η^{-1} exp(Ω(n^{1/3})) is absorbed into c′ for n ≥ n₀
--   - generalization: any algorithm using only Gaussian measurements → any Gaussian protocol on N copies: one POVM on ρ^{⊗N} with outcomes (y, u) ∈ ℝ^{2N(n+1)} × ℝ whose effect density is (2π)^{-N(n+1)} D(y) τ(y, u) D(y)† on u ∈ [0, 1], with a mean-zero Gaussian seed τ(y, u) that may depend measurably on the outcome, followed by an arbitrary function of the outcome; reason: the paper does not define the class; this class contains every reading of it (adaptive single-copy Gaussian measurements as in the published IsGaussianScheme, joint Gaussian measurements of several or all copies, adaptive Gaussian feed-forward on subsets of modes, classical randomness and arbitrary classical processing), so the lower bound for it implies the lower bound for each of them; the paper's proof (Eq. (80), Lemma 3 of [SW21]) bounds the total variation distance of the outcome laws on ρ₊^{⊗N} and ρ₋^{⊗N} for every measurement whose effects have nonnegative Wigner functions, which these have
--   - generalization: outputs |ψ̂±⟩ → the estimator outputs an arbitrary pure state, not necessarily Gaussian; reason: the theorem does not restrict the output; a lower bound against arbitrary pure outputs implies the one against pure Gaussian outputs (Lemma 5.9 treats every |ψ⟩)
--   - reading: outputs |ψ̂±⟩ with the guarantee d_IF(ρ±, |ψ̂±⟩) ≤ opt± + cη² with probability at least 2/3 → the same protocol and estimator meet the guarantee on ρ₊ with probability ≥ 2/3 and on ρ₋ with probability ≥ 2/3; reason: the algorithm does not know which of the two states it is given; |ψ̂±⟩ is its output on ρ±
--   - encoding: copy complexity N → the number N of copies in ρ^{⊗N}, any natural number; reason: the protocol measures N copies; N = 0 is included and excluded by the conclusion
--   - encoding: with probability at least 2/3 → an inner probability: a measurable set of outcomes of probability ≥ 2/3 on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: d_tr(ρ±, |0⟩^{⊗(n+1)}) ≤ η → the published BosonicLearn.traceDist (½‖·‖₁, in ℝ≥0∞) between ρ± and the vacuum projector on n + 1 modes, compared with ENNReal.ofReal η; reason: same values on density operators
--   - encoding: Gaussian measurement with seed state τ → the seed family τ(y, u) is entrywise measurable in the outcome; reason: a regularity condition: the seed is determined by the outcome law, so every protocol satisfies it; it only excludes non-measurable choices for which the density formula is not meaningful
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 5.6, printed pp. 52–53 (PDF pp. 55–56); proof on pp. 53–56 (PDF pp. 56–59), Eqs. (79), (80), Lemmas 5.7–5.9

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_AgnGaussTomo_Supplement_IsGaussianProtocol
import Definitions.Def_AgnGaussTomo_infid
import Definitions.Def_AgnGaussTomo_optG
import Definitions.Def_AgnGaussTomo_vacuum

open QAlgorithms.Papers.Independent.Dependency50.P33 (State PureState)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation Quadratures)

namespace AgnGaussTomo.Supplement

/-- **Theorem 5.6: Gaussian measurements need `η^{-1} exp(Ω(n^{1/3}))` copies to reach `opt + cη²`.**
Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810
(version of 3 Nov 2026), Theorem 5.6, printed pp. 52–53 (PDF pp. 55–56): "For universal constant
c > 0, sufficiently large n, and η ∈ (0, 1/4], there exist two (n + 1)-mode states ρ₊, ρ₋ satisfying
opt₊ = opt₋ = O(η), d_tr(ρ±, |0⟩^{⊗(n+1)}) ≤ η where opt± ≡ inf_{|ψ⟩∈G} d_IF(ρ±, |ψ⟩), such that any
algorithm using only Gaussian measurements that outputs |ψ̂±⟩ with the guarantee
d_IF(ρ±, |ψ̂±⟩) ≤ opt± + cη² with probability at least 2/3 must have copy complexity
N ≥ η^{-1} exp(Ω(n^{1/3}))."

**Formalization Note.**
1. Constants: `c` (the guarantee's slack), `C` (the `O(η)`), `c'` (the `Ω`) and `n₀` ("sufficiently
   large n") are universal, chosen before `n` and `η`; the states `ρ±` may depend on `n` and `η`.
   They are existentially quantified, not constructed (the proof's (79) is one choice).
2. The algorithm is any Gaussian protocol on `N` copies (`IsGaussianProtocol`): one measurement of
   `ρ^{⊗N}` (`WildeQIT.Schumacher.tensorPow N ρ`) whose effect density at the outcome `(y, u)` is a
   displaced mean-zero Gaussian seed that may depend on the outcome. This contains adaptive
   single-copy Gaussian schemes (the published `IsGaussianScheme`), joint Gaussian measurements of
   several or all copies, adaptive Gaussian feed-forward, and classical randomness (`u`), so the
   lower bound is stated for every reading of "any algorithm using only Gaussian measurements".
   The estimator is an arbitrary function of the outcome to **pure** states (`PureState`, not
   necessarily Gaussian). The same protocol and estimator must succeed on both `ρ₊` and `ρ₋`.
3. "With probability at least 2/3": some measurable set of outcomes of probability at least `2/3`
   consists of outcomes meeting the guarantee (inner probability, as in the published `Succeeds`).
4. `opt±` is `optG` (the infimum over the pure Gaussian states `G`); `d_IF(ρ, |ψ⟩⟨ψ|)` is `infid`
   (pure second argument); `d_tr` is the published `BosonicLearn.traceDist` (½‖·‖₁, in `ℝ≥0∞`);
   `|0⟩^{⊗(n+1)}` is `vacuum (n + 1)`; `n^{1/3}` is the real power. -/
theorem theorem_5_6 : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ c' : ℝ, 0 < c' ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      ∃ ρp ρm : State (Occupation (Fin (n + 1))),
        optG ρp = optG ρm ∧ optG ρp ≤ C * η ∧
        BosonicLearn.traceDist ρp.coefficients (vacuum (n + 1)) ≤ ENNReal.ofReal η ∧
        BosonicLearn.traceDist ρm.coefficients (vacuum (n + 1)) ≤ ENNReal.ofReal η ∧
        ∀ (N : ℕ) (P : BosonicLearn.FockPOVM (Fin N → Occupation (Fin (n + 1)))
            ((Quadratures (Fin N × Fin (n + 1)) → ℝ) × ℝ))
          (est : (Quadratures (Fin N × Fin (n + 1)) → ℝ) × ℝ → PureState (Occupation (Fin (n + 1)))),
          IsGaussianProtocol P →
          (∃ B : Set ((Quadratures (Fin N × Fin (n + 1)) → ℝ) × ℝ), MeasurableSet B ∧
            (∀ x ∈ B, infid ρp.coefficients (est x).1.coefficients ≤ optG ρp + c * η ^ 2) ∧
            ENNReal.ofReal (2 / 3) ≤
              P.law (WildeQIT.Schumacher.tensorPow N ρp.coefficients) B) →
          (∃ B : Set ((Quadratures (Fin N × Fin (n + 1)) → ℝ) × ℝ), MeasurableSet B ∧
            (∀ x ∈ B, infid ρm.coefficients (est x).1.coefficients ≤ optG ρm + c * η ^ 2) ∧
            ENNReal.ofReal (2 / 3) ≤
              P.law (WildeQIT.Schumacher.tensorPow N ρm.coefficients) B) →
          η⁻¹ * Real.exp (c' * (n : ℝ) ^ ((1 : ℝ) / 3)) ≤ (N : ℝ) := by sorry

end AgnGaussTomo.Supplement
