-- Prove2me | Theorems.Thm_AgnGaussTomo_theorem_3_4
-- name    : AgnGaussTomo.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:57.822959+00:00
-- url     : https://prove2.me/theorems/54eb41c0-f61a-4c96-95bf-ee210628bd0d
-- title:
--   Theorem 3.4 — robust iterative unsqueezing (corrected: max(1, log log κ) for log log‖V⁻¹‖)
-- statement:
--   There are universal constants $\overline{\mathrm{opt}}_{\mathrm{tr}}>0$ and $C>0$ such that the following holds for every $n$, $\delta\in(0,1/2)$, $\kappa\ge1$ and $\mathrm{opt}_{\mathrm{tr}}\in(0,\overline{\mathrm{opt}}_{\mathrm{tr}}]$. There is an adaptive scheme that **uses exclusively Gaussian measurements**, with
--
--   $$
--   N\le C\,n^3\,\mathrm{opt}_{\mathrm{tr}}^{-2}\,L(\kappa)\,\log^5(1/\delta)\qquad(L(\kappa)=\max\{1,\log\log\kappa\})
--   $$
--
--   copies and an estimator that always outputs a Gaussian state $\hat\pi$, such that for every $n$-mode state $\rho$ and every Gaussian state $\pi$ with covariance $V$, $\|V^{-1}\|_{\mathrm{op}}\le\kappa$ and $d_{\mathrm{tr}}(\rho,\pi)\le\mathrm{opt}_{\mathrm{tr}}$, with probability at least $1-\delta$,
--
--   $$
--   d_{\mathrm{tr}}(\rho,\hat\pi)\le n\cdot\widetilde O(\mathrm{opt}_{\mathrm{tr}}),\qquad \widetilde O(x)=C\,x\,(1+|\log x|)^C .
--   $$
--
--   Iterative unsqueezing removes the $\operatorname{tr}V^{-1}$ factor of Theorem 3.2; the remaining dependence on the squeezing is only doubly logarithmic, in the copy count.
--
--   Differences from the source:
--   - correction: log log ‖V^{-1}‖_op in the copy count → L(κ) = max(1, log log κ) for an upper bound κ ≥ ‖V^{-1}‖_op; reason: log log ‖V^{-1}‖_op ≤ 0 for ‖V^{-1}‖_op ≤ e (and −∞ at 1), so the printed count allows zero copies; but for one mode and the coherent states |α⟩, |−α⟩ with |α| = 1 (V = I) a zero-copy algorithm outputs a fixed state, which is at trace distance ≥ 0.49 from one of them since d_tr(|α⟩, |−α⟩) = √(1 − e^{−4}) > 0.98, contradicting the guarantee for small opt and ε; L agrees with log log once κ ≥ e^e
--   - reading: the algorithm's resources depend on ‖V^{-1}‖_op → the algorithm is given an upper bound κ ≥ 1 on ‖V^{-1}‖_op and must work for every state with ‖V^{-1}‖_op ≤ κ; reason: the algorithm runs K = log log ‖V^{-1}‖_op unsqueezing rounds (p. 15), so this quantity must be available to it; an algorithm that knows only an upper bound is at least as strong
--   - reading: O, Õ and opt̄_tr → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - reading: Õ(opt_tr) in the error → C·opt_tr·(1 + |log opt_tr|)^C; reason: Õ hides polylogarithmic factors of its argument
--   - reading: δ appears only in the copy count → success with probability at least 1 − δ for δ ∈ (0, 1/2); reason: δ is the failure probability of the robust estimator (Proposition 2.9, p. 13) and of the downstream Theorems 3.6 and 3.8
--   - reading: uses exclusively Gaussian measurements → every round's POVM is a Gaussian measurement (seed: a mean-zero Gaussian state) whose outcome also carries an independent uniform random number in [0, 1]; reason: the paper's algorithms are randomized (Proposition 2.9, Lemma 2.10), and classical randomness carries no quantum information
--   - generalization: there exists an algorithm → an adaptive scheme of Gaussian measurements on a number N of copies fixed in advance, with an estimator that is a function of the transcript, depending on n, δ, κ and opt_tr only; reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: opt_tr ≤ opt̄_tr → 0 < opt_tr ≤ opt̄_tr; reason: the copy count contains opt_tr^{-2}, which is undefined at opt_tr = 0
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.4, printed p. 16 (PDF p. 19); proof in App. A.2.2

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_IsGaussianPOVM
import Definitions.Def_AgnGaussTomo_LL
import Definitions.Def_AgnGaussTomo_opNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Theorem 3.4 (Robust "Energy-Independent" Tomography via Iterative Unsqueezing), with the
corrected `max(1, log log κ)`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic
States*, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.4, printed p. 16 (PDF p. 19): "Let ρ be
a n-mode state where d_tr(ρ, π) ≤ opt_tr ≤ opt̄_tr for Gaussian state π with covariance V. Then, there
exists an algorithm which takes O(n³ opt_tr^{-2} log log ‖V^{-1}‖_op log⁵(1/δ)) copies of ρ and uses
exclusively Gaussian measurements to output a Gaussian state π̂ satisfying
d_tr(ρ, π̂) ≤ n · Õ(opt_tr). (18)"

**Formalization Note.** Correction: `log log ‖V^{-1}‖_op` is replaced by `LL κ = max(1, log log κ)`
(the printed factor is `≤ 0` for `‖V^{-1}‖_op ≤ e`). The algorithm receives an upper bound
`κ ≥ ‖V^{-1}‖_op` (its number `K` of unsqueezing rounds depends on it, p. 15) and `opt_tr = o`; it never
sees `ρ`, `π`, `V`. Every round is a Gaussian measurement (`IsGaussianScheme`). `Õ(o)` is
`C·o·(1 + |log o|)^C`; the `O` and `opt̄_tr` are universal constants. "With probability at least
`1 − δ`, `δ ∈ (0, 1/2)`" is read into the statement. -/
theorem theorem_3_4 : ∃ optBarTr : ℝ, 0 < optBarTr ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (δ κ o : ℝ), 0 < δ → δ < 1 / 2 → 1 ≤ κ → 0 < o → o ≤ optBarTr →
      ∃ (N : ℕ) (S : BosonicLearn.AdaptiveScheme n N ((Fin n ⊕ Fin n → ℝ) × ℝ))
        (est : (Fin N → (Fin n ⊕ Fin n → ℝ) × ℝ) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 3 / o ^ 2 * LL κ * Real.log (1 / δ) ^ 5 ∧
        IsGaussianScheme S ∧
        (∀ x, est x ∈ OptGaussTomo.boseGauss n) ∧
        ∀ (ρ π : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
          (V : OscillatorCovariance (Fin n)),
          GaussianAt π.coefficients m V → opNorm V⁻¹ ≤ κ →
          BosonicLearn.traceDist ρ.coefficients π.coefficients ≤ ENNReal.ofReal o →
          Succeeds S ρ.coefficients (fun x =>
            BosonicLearn.traceDist ρ.coefficients (est x).coefficients ≤
              ENNReal.ofReal ((n : ℝ) * (C * o * (1 + |Real.log o|) ^ C))) δ := by sorry

end AgnGaussTomo
