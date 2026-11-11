-- Prove2me | Theorems.Thm_AgnGaussTomo_theorem_3_6
-- name    : AgnGaussTomo.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:02.412174+00:00
-- url     : https://prove2.me/theorems/611ecebd-9a35-442e-bbfc-46da64559e5b
-- title:
--   Theorem 3.6 — robust pure-state warm start with Gaussian measurements (corrected: max(1, log log κ) for log log‖V⁻¹‖)
-- statement:
--   There are universal constants $\overline{\mathrm{opt}}_{\mathrm{tr}}>0$ and $C>0$ such that for every $n$, $\epsilon>0$, $\delta\in(0,1/2)$ and $\kappa\ge1$ there is an adaptive scheme that **uses exclusively Gaussian measurements**, with
--
--   $$
--   N\le C\,\frac{n^2}{\epsilon^2}\,L(\kappa)\log^5(1/\delta)\,\log^C\!\Big(e+n+\frac1\epsilon+\frac1\delta+L(\kappa)\Big)
--   $$
--
--   copies and an estimator that always outputs a pure Gaussian state $|\hat\psi\rangle$, such that for every $n$-mode state $\rho$, every pure Gaussian state $|\psi\rangle$ with covariance $V$, $\|V^{-1}\|_{\mathrm{op}}\le\kappa$, and every $\mathrm{opt}_{\mathrm{tr}}\in[0,\overline{\mathrm{opt}}_{\mathrm{tr}}]$ with $d_{\mathrm{tr}}(\rho,|\psi\rangle\langle\psi|)\le\mathrm{opt}_{\mathrm{tr}}$, with probability at least $1-\delta$,
--
--   $$
--   d_{\mathrm{tr}}(\rho,|\hat\psi\rangle\langle\hat\psi|)\le\widetilde O(\mathrm{opt}_{\mathrm{tr}})+\epsilon,\qquad\widetilde O(x)=C\,x\,(1+|\log x|)^C .
--   $$
--
--   Here $L(\kappa)=\max\{1,\log\log\kappa\}$. This is the warm start of the high-fidelity algorithm: a guarantee with no mode or energy factor, using Gaussian measurements only.
--
--   Differences from the source:
--   - correction: log log ‖V^{-1}‖_op in the copy count → L(κ) = max(1, log log κ) for an upper bound κ ≥ ‖V^{-1}‖_op; reason: log log ‖V^{-1}‖_op ≤ 0 for ‖V^{-1}‖_op ≤ e (and −∞ at 1), so the printed count allows zero copies; but for one mode and the coherent states |α⟩, |−α⟩ with |α| = 1 (V = I) a zero-copy algorithm outputs a fixed state, which is at trace distance ≥ 0.49 from one of them since d_tr(|α⟩, |−α⟩) = √(1 − e^{−4}) > 0.98, contradicting the guarantee for small opt and ε; L agrees with log log once κ ≥ e^e
--   - reading: the algorithm's resources depend on ‖V^{-1}‖_op → the algorithm is given an upper bound κ ≥ 1 on ‖V^{-1}‖_op and must work for every state with ‖V^{-1}‖_op ≤ κ; reason: the algorithm runs K = log log ‖V^{-1}‖_op unsqueezing rounds (p. 15), so this quantity must be available to it; an algorithm that knows only an upper bound is at least as strong
--   - reading: Õ(n² ε^{-2} log log ‖V^{-1}‖_op log⁵(1/δ)) copies → N ≤ C·n²·ε^{-2}·L(κ)·log⁵(1/δ)·log(e + n + 1/ε + 1/δ + L(κ))^C; reason: Õ hides polylogarithmic factors of the parameters (κ enters only through L(κ)); one universal C
--   - reading: the algorithm for given ε, δ → the scheme depends on n, ε, δ and κ only, not on opt_tr; reason: opt_tr does not enter the copy count; an algorithm that does not know it is at least as strong
--   - reading: Õ and opt̄_tr → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - reading: Õ(opt_tr) in the error → C·opt_tr·(1 + |log opt_tr|)^C; reason: Õ hides polylogarithmic factors of its argument
--   - reading: uses exclusively Gaussian measurements → every round's POVM is a Gaussian measurement (seed: a mean-zero Gaussian state) whose outcome also carries an independent uniform random number in [0, 1]; reason: the paper's algorithms are randomized (Proposition 2.9, Lemma 2.10), and classical randomness carries no quantum information
--   - generalization: there exists an algorithm → an adaptive scheme of Gaussian measurements on a number N of copies fixed in advance, with an estimator that is a function of the transcript; reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: opt_tr → 0 ≤ opt_tr; reason: a trace-distance bound; it excludes only negative values
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.6, printed p. 17 (PDF p. 20); proof on p. 18 (PDF p. 21)

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

/-- **Theorem 3.6: robust pure-state warm start with Gaussian measurements, with the corrected
`max(1, log log κ)`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*,
arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.6, printed p. 17 (PDF p. 20): "Let ρ be an n-mode
state where d_tr(ρ, |ψ⟩⟨ψ|) ≤ opt_tr ≤ opt̄_tr for pure Gaussian state |ψ⟩ with covariance V. Then,
given ε > 0 and δ ∈ (0, 1/2), there exists an algorithm which takes
Õ(n² ε^{-2} log log ‖V^{-1}‖_op log⁵(1/δ)) copies of ρ and uses exclusively Gaussian measurements to
output a pure Gaussian state |ψ̂⟩ satisfying d_tr(ρ, |ψ̂⟩⟨ψ̂|) ≤ Õ(opt_tr) + ε. (19) with probability at
least 1 − δ."

**Formalization Note.** Correction: `log log ‖V^{-1}‖_op` → `LL κ = max(1, log log κ)`. The scheme
depends on `n, ε, δ` and an upper bound `κ ≥ ‖V^{-1}‖_op` only (not on `opt_tr`, which does not enter
the copy count). `Õ(X)` in the copy count is `C·X·log(e + n + 1/ε + 1/δ + LL κ)^C`; `Õ(o)` in the
error is `C·o·(1 + |log o|)^C`; `opt̄_tr` and `C` are universal. Every round is a Gaussian
measurement and every output is a pure Gaussian state. -/
theorem theorem_3_6 : ∃ optBarTr : ℝ, 0 < optBarTr ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ε δ κ : ℝ), 0 < ε → 0 < δ → δ < 1 / 2 → 1 ≤ κ →
      ∃ (N : ℕ) (S : BosonicLearn.AdaptiveScheme n N ((Fin n ⊕ Fin n → ℝ) × ℝ))
        (est : (Fin N → (Fin n ⊕ Fin n → ℝ) × ℝ) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 / ε ^ 2 * LL κ * Real.log (1 / δ) ^ 5 *
          Real.log (Real.exp 1 + n + 1 / ε + 1 / δ + LL κ) ^ C ∧
        IsGaussianScheme S ∧
        (∀ x, est x ∈ OptGaussTomo.bosePure n) ∧
        ∀ (ρ ψ : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
          (V : OscillatorCovariance (Fin n)) (o : ℝ),
          ψ ∈ OptGaussTomo.bosePure n → GaussianAt ψ.coefficients m V → opNorm V⁻¹ ≤ κ →
          BosonicLearn.traceDist ρ.coefficients ψ.coefficients ≤ ENNReal.ofReal o →
          0 ≤ o → o ≤ optBarTr →
          Succeeds S ρ.coefficients (fun x =>
            BosonicLearn.traceDist ρ.coefficients (est x).coefficients ≤
              ENNReal.ofReal (C * o * (1 + |Real.log o|) ^ C + ε)) δ := by sorry

end AgnGaussTomo
