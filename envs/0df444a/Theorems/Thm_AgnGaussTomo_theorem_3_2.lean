-- Prove2me | Theorems.Thm_AgnGaussTomo_theorem_3_2
-- name    : AgnGaussTomo.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:25.480793+00:00
-- url     : https://prove2.me/theorems/8af6015f-6002-4bf5-813d-d315c1ca94e8
-- title:
--   Theorem 3.2 — robust heterodyne tomography
-- statement:
--   There are universal constants $\overline{\mathrm{opt}}_{\mathrm{tr}}>0$ and $C>0$ such that the following holds for every $n$, every $\delta\in(0,1/2)$ and every $\mathrm{opt}_{\mathrm{tr}}\in(0,\overline{\mathrm{opt}}_{\mathrm{tr}}]$. There is an adaptive single-copy measurement scheme using
--
--   $$
--   N\le C\,\frac{n^2\log^5(1/\delta)}{\mathrm{opt}_{\mathrm{tr}}^2}\,\log^C\!\Big(e+n+\frac1\delta+\frac1{\mathrm{opt}_{\mathrm{tr}}}\Big)
--   $$
--
--   copies, with an estimator that always outputs a Gaussian state $\hat\pi$, such that for every $n$-mode state $\rho$ and every Gaussian state $\pi$ with mean $m$ and covariance $V$ satisfying $d_{\mathrm{tr}}(\rho,\pi)\le\mathrm{opt}_{\mathrm{tr}}$, with probability at least $1-\delta$ both
--
--   $$
--   d_{\mathrm{tr}}(\rho,\hat\pi)\le C\,(n+\operatorname{tr}V^{-1})\,\widetilde{O}(\mathrm{opt}_{\mathrm{tr}})\quad\text{and}\quad d_{\mathrm{tr}}(\rho,\hat\pi)\le C\,E(\pi)\,\widetilde{O}(\mathrm{opt}_{\mathrm{tr}})
--   $$
--
--   hold, where $\widetilde O(x)=C\,x\,(1+|\log x|)^C$ and $E(\pi)=\tfrac14\operatorname{tr}V+\tfrac12\|m\|_2^2$.
--
--   This is heterodyne tomography made robust to an $\mathrm{opt}_{\mathrm{tr}}$-fraction of arbitrary corruption, at the price of an energy factor in the error.
--
--   Differences from the source:
--   - reading: Õ(n² log⁵(1/δ)/opt_tr²) copies → N ≤ C·n²·log⁵(1/δ)·opt_tr^{-2}·log(e + n + 1/δ + 1/opt_tr)^C; reason: Õ hides polylogarithmic factors of the parameters; one universal C serves as factor and exponent
--   - reading: ≲, Õ and opt̄_tr → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - reading: Õ(opt_tr) in the error → C·opt_tr·(1 + |log opt_tr|)^C; reason: Õ hides polylogarithmic factors of its argument
--   - reading: δ appears only in the copy count → success with probability at least 1 − δ for δ ∈ (0, 1/2); reason: δ is the failure probability of the robust estimator (Proposition 2.9, p. 13) and of the downstream Theorems 3.6 and 3.8
--   - generalization: there exists an algorithm → an adaptive single-copy measurement scheme on a number N of copies fixed in advance, with an estimator that is a function of the transcript, depending on n, δ and opt_tr only; reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: the chain d_tr(ρ, π̂) ≲ (n + tr V^{-1})·Õ(opt_tr) ≲ E(π)·Õ(opt_tr) → two conclusions: d_tr(ρ, π̂) ≤ C(n + tr V^{-1})Õ(opt_tr) and d_tr(ρ, π̂) ≤ C·E(π)·Õ(opt_tr); reason: these are the two bounds on d_tr(ρ, π̂) the chain asserts
--   - encoding: opt_tr ≤ opt̄_tr → 0 < opt_tr ≤ opt̄_tr; reason: the copy count contains opt_tr^{-2}, which is undefined at opt_tr = 0
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
--   - encoding: covariances and means in the order (q₁, …, qₙ, p₁, …, pₙ) → the interleaved order (q₁, p₁, …, qₙ, pₙ) of the published GaussianAt, with symplectic and Williamson data in the grouped order; reason: a relabelling of the same quadratures; norms, traces and the Loewner order are unchanged
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.2, printed p. 15 (PDF p. 18); proof in App. A.2.1, pp. 69–71

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_energy

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14 (GaussianAt InterleavedQuadrature OscillatorCovariance)

namespace AgnGaussTomo

/-- **Theorem 3.2 (Robust Heterodyne Tomography).** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Theorem 3.2, printed p. 15
(PDF p. 18): "Let ρ be an n-mode state where d_tr(ρ, π) ≤ opt_tr ≤ opt̄_tr for some Gaussian state π
with mean m and covariance V. Then, there exists an algorithm which given Õ(n² log⁵(1/δ)/opt_tr²)
copies of ρ constructs a Gaussian state π̂ with the semi-agnostic guarantee:
d_tr(ρ, π̂) ≲ (n + tr V^{-1}) · Õ(opt_tr) ≲ E(π) · Õ(opt_tr). (17)"

**Formalization Note.** `opt̄_tr` and the constants of `Õ`, `≲` are universal (chosen before `n`).
The algorithm is an adaptive single-copy scheme with `N` copies and an estimator of the transcript;
it may depend on `n`, `δ` and `opt_tr = o` (its copy count does), never on `ρ`, `π`, `m`, `V`.
`Õ(X)` in the copy count is `C·X·log(e + n + 1/δ + 1/o)^C`; `Õ(o)` in the error is
`C·o·(1 + |log o|)^C`. "With probability at least `1 − δ`, `δ ∈ (0, 1/2)`" is read into the
statement (`δ` appears only in the copy count as printed). Both inequalities of (17) are
conclusions about `d_tr(ρ, π̂)`. Trace distances are compared in `ℝ≥0∞`. -/
theorem theorem_3_2 : ∃ optBarTr : ℝ, 0 < optBarTr ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (δ o : ℝ), 0 < δ → δ < 1 / 2 → 0 < o → o ≤ optBarTr →
      ∃ (N : ℕ) (O : Type) (_ : MeasurableSpace O) (S : BosonicLearn.AdaptiveScheme n N O)
        (est : (Fin N → O) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 * Real.log (1 / δ) ^ 5 / o ^ 2 *
          Real.log (Real.exp 1 + n + 1 / δ + 1 / o) ^ C ∧
        (∀ x, est x ∈ OptGaussTomo.boseGauss n) ∧
        ∀ (ρ π : State (Occupation (Fin n))) (m : InterleavedQuadrature (Fin n) → ℝ)
          (V : OscillatorCovariance (Fin n)),
          GaussianAt π.coefficients m V →
          BosonicLearn.traceDist ρ.coefficients π.coefficients ≤ ENNReal.ofReal o →
          Succeeds S ρ.coefficients (fun x =>
            BosonicLearn.traceDist ρ.coefficients (est x).coefficients ≤
                ENNReal.ofReal (C * ((n : ℝ) + V⁻¹.trace) * (o * (1 + |Real.log o|) ^ C)) ∧
            BosonicLearn.traceDist ρ.coefficients (est x).coefficients ≤
                ENNReal.ofReal (C * energy m V * (o * (1 + |Real.log o|) ^ C))) δ := by sorry

end AgnGaussTomo
