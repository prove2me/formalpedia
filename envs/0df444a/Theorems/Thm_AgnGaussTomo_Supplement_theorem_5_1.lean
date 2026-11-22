-- Prove2me | Theorems.Thm_AgnGaussTomo_Supplement_theorem_5_1
-- name    : AgnGaussTomo.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:01:52.141424+00:00
-- url     : https://prove2.me/theorems/52d4a0b3-0b40-40f2-bf5c-04830015fab1
-- title:
--   Theorem 5.1 — Gaussian measurements reach infidelity $O(\mathrm{opt})+\epsilon$ from $\widetilde O(n^2/\epsilon)$ copies (corrected: max(1, log log κ) for log log‖V⁻¹‖)
-- statement:
--   There are universal constants $\overline{\mathrm{opt}}\in(0,1)$ and $C>0$ such that for every number of modes $n$, every $\epsilon>0$, $\delta\in(0,1/2)$ and $\kappa\ge1$ there is an adaptive scheme that **uses only Gaussian measurements**, on
--
--   $$
--   N\le C\,\frac{n^2}{\epsilon}\,L(\kappa)\log^5(1/\delta)\,\log^C\!\Big(e+n+\frac1\epsilon+\frac1\delta+L(\kappa)\Big)
--   $$
--
--   copies, with an estimator that always outputs a pure Gaussian state $|\hat\psi\rangle$, such that the following holds. For every $n$-mode state $\rho$ (a density operator on the Fock space, mixed allowed, of any energy), every pure Gaussian state $|\psi\rangle$ with covariance $V$, $\|V^{-1}\|_{\mathrm{op}}\le\kappa$, and every $\mathrm{opt}\le\overline{\mathrm{opt}}$ with $d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)\le\mathrm{opt}$, with probability at least $1-\delta$,
--
--   $$
--   d_{\mathrm{IF}}(\rho,|\hat\psi\rangle\langle\hat\psi|)\le C\,\mathrm{opt}+\epsilon .
--   $$
--
--   Here $d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|)=1-\langle\psi|\rho|\psi\rangle$ is the infidelity, $L(\kappa)=\max\{1,\log\log\kappa\}$, the covariance is normalized so that the vacuum has $V=I$, and a Gaussian measurement is a POVM $(2\pi)^{-n}D(y)\tau D(y)^\dagger d^{2n}y$ with a mean-zero Gaussian seed state $\tau$. The scheme measures the copies one at a time, each with a Gaussian measurement chosen from the earlier outcomes, and it is given only $n$, $\epsilon$, $\delta$ and $\kappa$.
--
--   This is the positive half of the paper's separation between Gaussian and non-Gaussian measurements: Gaussian measurements alone improve the warm start $\widetilde O(\mathrm{opt})+\epsilon$ to the semi-agnostic guarantee $O(\mathrm{opt})+\epsilon$ in infidelity, while Theorem 5.6 shows they cannot reach $\mathrm{opt}+\epsilon$ efficiently.
--
--   Differences from the source:
--   - correction: log log ‖V^{-1}‖_op in the copy count → L(κ) = max(1, log log κ) for an upper bound κ ≥ ‖V^{-1}‖_op; reason: log log ‖V^{-1}‖_op ≤ 0 for ‖V^{-1}‖_op ≤ e (and −∞ at 1), so the printed count allows zero copies; but for one mode and ρ one of the coherent states |α⟩, |−α⟩ with |α| = 1 (V = I, opt = 0) a zero-copy algorithm outputs a fixed pure state, whose infidelity with one of them is at least 0.24, since d_tr(|α⟩, |−α⟩) = √(1 − e^{−4}) > 0.98 and d_tr = √d_IF for pure states, contradicting the guarantee for ε < 0.24; L agrees with log log once κ ≥ e^e. This is the correction of the published Theorems 3.4, 3.6 and 3.8
--   - reading: the algorithm's resources depend on ‖V^{-1}‖_op → the algorithm is given an upper bound κ ≥ 1 on ‖V^{-1}‖_op and must work for every state with ‖V^{-1}‖_op ≤ κ; reason: the algorithm runs log log ‖V^{-1}‖_op unsqueezing rounds (p. 15), so this quantity must be available to it; an algorithm that knows only an upper bound is at least as strong
--   - reading: Õ(n² ε^{-1} log log ‖V^{-1}‖_op log⁵(1/δ)) copies → N ≤ C·n²·ε^{-1}·L(κ)·log⁵(1/δ)·log(e + n + 1/ε + 1/δ + L(κ))^C; reason: Õ hides polylogarithmic factors of the parameters (κ enters only through L(κ)); one universal C; ε^{-1} multiplies every factor, as printed
--   - reading: O(opt) + ε → C·opt + ε with the same universal constant C; reason: O hides an absolute constant; one constant for the copy count and the error is equivalent to two
--   - reading: opt ≤ opt̄ → opt̄ is a universal constant in (0, 1), chosen with C before n and every other parameter; opt is any number with d_IF(ρ, ψ) ≤ opt ≤ opt̄; reason: Theorem 3.8 and Theorem 1.1 call opt̄ a universal constant in (0, 1); Theorem 5.1 uses the same symbol
--   - reading: given ε > 0 and δ ∈ (0, 1/2), there exists an algorithm → the scheme and estimator depend on n, ε, δ and κ only, not on ρ, ψ, V or opt; reason: opt does not enter the copy count; an algorithm that does not know it is at least as strong
--   - reading: uses only Gaussian measurements → every round's POVM is a Gaussian measurement (seed: a mean-zero Gaussian state) whose outcome also carries an independent uniform random number in [0, 1]; reason: the paper's algorithms are randomized (Proposition 2.9, Corollary 5.5), and classical randomness carries no quantum information; this is the published IsGaussianScheme of Theorems 3.4 and 3.6
--   - generalization: there exists an algorithm → an adaptive single-copy scheme of Gaussian measurements on a number N of copies fixed in advance, with an estimator that is a function of the transcript; reason: this is one kind of algorithm using only Gaussian measurements, so the existence claim specializes to the source's
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: covariance V in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt; reason: a relabelling of the same quadratures; ‖V^{-1}‖_op is unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 5.1, printed p. 49 (PDF p. 52); proof on pp. 49–52 (PDF pp. 52–55)

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_IsGaussianPOVM
import Definitions.Def_AgnGaussTomo_infid
import Definitions.Def_AgnGaussTomo_LL
import Definitions.Def_AgnGaussTomo_opNorm

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo.Supplement

/-- **Theorem 5.1: Gaussian measurements refine to `O(opt) + ε` in infidelity, with the corrected
`max(1, log log κ)`.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian Structure in Bosonic States*,
arXiv:2610.06810 (version of 3 Nov 2026), Theorem 5.1, printed p. 49 (PDF p. 52): "Let ρ be an n-mode
state where d_IF(ρ, |ψ⟩⟨ψ|) ≤ opt ≤ opt̄ for pure Gaussian state |ψ⟩ with covariance V. Then, given
ε > 0 and δ ∈ (0, 1/2), there exists an algorithm takes Õ(n² ε^{-1} log log ‖V^{-1}‖_op log⁵(1/δ))
copies of ρ and uses only Gaussian measurements to output a pure Gaussian state |ψ̂⟩ satisfying
d_IF(ρ, |ψ̂⟩⟨ψ̂|) ≤ O(opt) + ε with probability at least 1 − δ."

**Formalization Note.**
1. Correction (as in the published Theorems 3.4, 3.6, 3.8): `log log ‖V^{-1}‖_op` → `LL κ =
   max(1, log log κ)`; the printed factor is `≤ 0` (or `−∞`) for `‖V^{-1}‖_op ≤ e`, which would allow
   zero copies, and zero copies cannot learn the coherent states `|±α⟩`, `|α| = 1`.
2. The algorithm is an adaptive scheme on a number `N` of copies fixed in advance, every round a
   Gaussian measurement (`IsGaussianScheme`, seed form of p. 10, with an independent uniform random
   number for classical randomness), and a deterministic estimator of the transcript. It is given
   `n, ε, δ` and an upper bound `κ ≥ ‖V^{-1}‖_op`, and never sees `ρ`, `ψ`, `V` or `opt`.
3. `Õ(X)` in the copy count is `C·X·log(e + n + 1/ε + 1/δ + LL κ)^C`: one product, `ε^{-1}` multiplies
   every factor. `O(opt)` in the error is `C·opt` with the same universal `C`; `opt̄ ∈ (0, 1)` is universal.
   Both are chosen before every other parameter.
4. Every output is a pure Gaussian state (`OptGaussTomo.bosePure`); `d_IF(ρ, |ψ⟩⟨ψ|) = 1 − ⟨ψ|ρ|ψ⟩`
   (`infid`, pure second argument). `opt` is any number with `d_IF(ρ, ψ) ≤ opt ≤ opt̄`. -/
theorem theorem_5_1 : ∃ optBar : ℝ, 0 < optBar ∧ optBar < 1 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ε δ κ : ℝ), 0 < ε → 0 < δ → δ < 1 / 2 → 1 ≤ κ →
      ∃ (N : ℕ) (S : BosonicLearn.AdaptiveScheme n N ((Fin n ⊕ Fin n → ℝ) × ℝ))
        (est : (Fin N → (Fin n ⊕ Fin n → ℝ) × ℝ) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 / ε * LL κ * Real.log (1 / δ) ^ 5 *
          Real.log (Real.exp 1 + n + 1 / ε + 1 / δ + LL κ) ^ C ∧
        IsGaussianScheme S ∧
        (∀ x, est x ∈ OptGaussTomo.bosePure n) ∧
        ∀ (ρ ψ : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
          (V : OscillatorCovariance (Fin n)) (opt : ℝ),
          ψ ∈ OptGaussTomo.bosePure n → GaussianAt ψ.coefficients m V → opNorm V⁻¹ ≤ κ →
          infid ρ.coefficients ψ.coefficients ≤ opt → opt ≤ optBar →
          Succeeds S ρ.coefficients
            (fun x => infid ρ.coefficients (est x).coefficients ≤ C * opt + ε) δ := by sorry

end AgnGaussTomo.Supplement
