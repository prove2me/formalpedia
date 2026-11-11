-- Prove2me | Theorems.Thm_AgnGaussTomo_theorem_3_8
-- name    : AgnGaussTomo.theorem_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:40.209998+00:00
-- url     : https://prove2.me/theorems/e579a281-4c2d-4a04-ab9c-a057dc84c1a0
-- title:
--   Theorem 3.8 — high-fidelity agnostic tomography of pure Gaussian states (corrected: max(1, log log κ) for log log‖V⁻¹‖)
-- statement:
--   There are universal constants $\overline{\mathrm{opt}}\in(0,1)$ and $C>0$ such that for every number of modes $n$, every $\epsilon>0$, every $\delta\in(0,1/2)$ and every $\kappa\ge1$ there is an adaptive single-copy measurement scheme on
--
--   $$
--   N\le C\,n^2\Big(L(\kappa)\log^5(1/\delta)+\frac1\epsilon\Big)\log^C\!\Big(e+n+\frac1\epsilon+\frac1\delta+L(\kappa)\Big),\qquad L(\kappa)=\max\{1,\log\log\kappa\},
--   $$
--
--   copies, with an estimator that always outputs a pure Gaussian state $|\hat\psi\rangle$, such that the following holds. Let $\rho$ be an arbitrary $n$-mode bosonic state and $|\psi\rangle$ a pure Gaussian state with covariance $V$, $\|V^{-1}\|_{\mathrm{op}}\le\kappa$, and let $\mathrm{opt}$ be a number with
--
--   $$
--   d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)\le\mathrm{opt}\le\overline{\mathrm{opt}} .
--   $$
--
--   Then, with probability at least $1-\delta$,
--
--   $$
--   d_{\mathrm{IF}}(\rho,|\hat\psi\rangle\langle\hat\psi|)\le\mathrm{opt}+\epsilon .
--   $$
--
--   In the high-fidelity regime the learner thus competes with the best pure Gaussian approximation to an arbitrary, possibly non-Gaussian and mixed, state, with a copy count quadratic in the number of modes and only doubly logarithmic in the squeezing.
--
--   Differences from the source:
--   - correction: log log ‖V^{-1}‖_op in the copy count → L(κ) = max(1, log log κ) for an upper bound κ ≥ ‖V^{-1}‖_op; reason: log log ‖V^{-1}‖_op ≤ 0 for ‖V^{-1}‖_op ≤ e (and −∞ at 1), so the printed count allows zero copies; but for one mode and the coherent states |α⟩, |−α⟩ with |α| = 1 (V = I) a zero-copy algorithm outputs a fixed state, which is at trace distance ≥ 0.49 from one of them since d_tr(|α⟩, |−α⟩) = √(1 − e^{−4}) > 0.98, contradicting the guarantee for small opt and ε; L agrees with log log once κ ≥ e^e
--   - reading: the algorithm's resources depend on ‖V^{-1}‖_op → the algorithm is given an upper bound κ ≥ 1 on ‖V^{-1}‖_op and must work for every state with ‖V^{-1}‖_op ≤ κ; reason: the algorithm runs K = log log ‖V^{-1}‖_op unsqueezing rounds (p. 15), so this quantity must be available to it; an algorithm that knows only an upper bound is at least as strong
--   - reading: Õ(n²(log log ‖V^{-1}‖_op log⁵(1/δ) + ε^{-1})) copies → N ≤ C·n²·(L(κ)·log⁵(1/δ) + 1/ε)·log(e + n + 1/ε + 1/δ + L(κ))^C; reason: Õ hides polylogarithmic factors of n, 1/ε, 1/δ and L(κ); the narrower reading with no log(1/δ) factor beside 1/ε is false (two hypotheses at infidelity distance ~ε need ~log(1/δ)/ε copies)
--   - reading: a universal constant opt̄ → opt̄ ∈ (0, 1), chosen with C before every other parameter; reason: Theorem 1.1 (p. 2), the informal version, specifies opt̄ ∈ (0, 1)
--   - generalization: there exists an algorithm → an adaptive single-copy measurement scheme on a number N of copies fixed in advance, with an estimator that is a function of the transcript, depending on n, ε, δ and κ only (not on ρ, ψ, V or opt); reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
--   - encoding: d_IF(ρ, |ψ̂⟩⟨ψ̂|) = 1 − F(ρ, |ψ̂⟩⟨ψ̂|) → infid ρ σ = 1 − Re Σ_i Σ_j ρ_ij σ_ji (Fock-basis series) with σ pure (the output or ψ); reason: for pure σ = |ψ⟩⟨ψ|, F(ρ, σ) = ⟨ψ|ρ|ψ⟩ = tr(ρσ), so the values agree on every instance
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.8, printed p. 18 (PDF p. 21) (formal version of Theorem 1.1, p. 2)

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_infid
import Definitions.Def_AgnGaussTomo_LL
import Definitions.Def_AgnGaussTomo_opNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Theorem 3.8: agnostic tomography of pure Gaussian states in the high-fidelity regime, with the
corrected `max(1, log log κ)`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic
States*, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.8, printed p. 18 (PDF p. 21): "Let ρ be an
arbitrary n-mode bosonic state and |ψ⟩ be a pure Gaussian state with covariance V such that
d_IF(ρ, |ψ⟩⟨ψ|) ≤ opt ≤ opt̄ for universal constant opt̄. Then, for given ε > 0 and δ ∈ (0, 1/2), there
exists an algorithm which takes Õ(n²(log log ‖V^{-1}‖_op log⁵(1/δ) + ε^{-1})) copies and outputs a pure
Gaussian state |ψ̂⟩ satisfying d_IF(ρ, |ψ̂⟩⟨ψ̂|) ≤ opt + ε with probability at least 1 − δ."
(Informal version: Theorem 1.1, p. 2, "a universal constant opt̄ ∈ (0, 1)".)

**Formalization Note.**
1. Correction: `log log ‖V^{-1}‖_op` → `LL κ = max(1, log log κ)` (the printed factor is `≤ 0`, or
   `−∞`, for `‖V^{-1}‖_op ≤ e`, which would allow zero copies).
2. The algorithm is an adaptive single-copy scheme on a number `N` of copies fixed in advance, with a
   deterministic estimator of the transcript; it is given `n, ε, δ` and an upper bound
   `κ ≥ ‖V^{-1}‖_op`, and works for every `ρ`, every pure Gaussian `ψ` with `‖V^{-1}‖_op ≤ κ` and every
   `opt` with `d_IF(ρ, ψ) ≤ opt ≤ opt̄`. It never sees `ρ`, `ψ`, `V` or `opt`.
3. `Õ(X)` is `C·X·log(e + n + 1/ε + 1/δ + LL κ)^C` with one universal `C`; `opt̄ ∈ (0, 1)` is universal.
4. Every output is a pure Gaussian state (`OptGaussTomo.bosePure`); `d_IF(ρ, |ψ⟩⟨ψ|) = 1 − ⟨ψ|ρ|ψ⟩`
   (`infid`). `ρ` is any density operator, of any energy. -/
theorem theorem_3_8 : ∃ optBar : ℝ, 0 < optBar ∧ optBar < 1 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ε δ κ : ℝ), 0 < ε → 0 < δ → δ < 1 / 2 → 1 ≤ κ →
      ∃ (N : ℕ) (O : Type) (_ : MeasurableSpace O) (S : BosonicLearn.AdaptiveScheme n N O)
        (est : (Fin N → O) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 * (LL κ * Real.log (1 / δ) ^ 5 + 1 / ε) *
          Real.log (Real.exp 1 + n + 1 / ε + 1 / δ + LL κ) ^ C ∧
        (∀ x, est x ∈ OptGaussTomo.bosePure n) ∧
        ∀ (ρ ψ : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
          (V : OscillatorCovariance (Fin n)) (opt : ℝ),
          ψ ∈ OptGaussTomo.bosePure n → GaussianAt ψ.coefficients m V → opNorm V⁻¹ ≤ κ →
          infid ρ.coefficients ψ.coefficients ≤ opt → opt ≤ optBar →
          Succeeds S ρ.coefficients
            (fun x => infid ρ.coefficients (est x).coefficients ≤ opt + ε) δ := by sorry

end AgnGaussTomo
