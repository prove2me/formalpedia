-- Prove2me | Theorems.Thm_AgnGaussTomo_proposition_3_15
-- name    : AgnGaussTomo.proposition_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:33.31821+00:00
-- url     : https://prove2.me/theorems/6fe92793-4379-48ea-91e1-8d08d41495f2
-- title:
--   Proposition 3.15 — refinement to $\mathrm{opt}+\epsilon$ near the vacuum
-- statement:
--   There are universal constants $\gamma_1>0$ and $C>0$ such that for every $n$, $\epsilon\in(0,1)$ and $\delta\in(0,1/2)$ there is an adaptive single-copy measurement scheme using
--
--   $$
--   N\le C\,\frac{n^2}{\epsilon}\log(1/\delta)\,\log^C\!\Big(e+n+\frac1\epsilon+\frac1\delta\Big)
--   $$
--
--   copies, with an estimator that always outputs a pure Gaussian state $|\hat\psi\rangle$, such that for every $n$-mode state $\rho$ with $d_{\mathrm{tr}}(\rho,|0\rangle\langle0|)\le\gamma_1$, with probability at least $1-\delta$,
--
--   $$
--   d_{\mathrm{IF}}(\rho,|\hat\psi\rangle\langle\hat\psi|)\le\mathrm{opt}+\epsilon,\qquad\mathrm{opt}=\inf_{|\psi\rangle\in\mathcal G}d_{\mathrm{IF}}(\rho,|\psi\rangle\langle\psi|).
--   $$
--
--   Starting from a state already close to the vacuum, this stage reaches the optimal error $\mathrm{opt}+\epsilon$ rather than a polylogarithmic multiple of $\mathrm{opt}$.
--
--   Differences from the source:
--   - reading: Õ(n² ε^{-1} log(1/δ)) copies → N ≤ C·n²·ε^{-1}·log(1/δ)·log(e + n + 1/ε + 1/δ)^C; reason: Õ hides polylogarithmic factors of the parameters; one universal C
--   - reading: γ₁ and Õ → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - generalization: there exists an algorithm → an adaptive single-copy scheme on a number N of copies fixed in advance, with an estimator that is a function of the transcript, depending on n, ε and δ only; reason: this is one kind of algorithm, so the existence claim specializes to the source's; the scheme depends only on the parameters named in the statement, never on the unknown state
--   - encoding: with probability at least 1 − δ → an inner probability: a measurable set of transcripts of probability ≥ 1 − δ on which the guarantee holds; reason: the guarantee need not define a measurable event; same meaning for measurable events
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
--   - encoding: d_IF(ρ, |ψ̂⟩⟨ψ̂|) = 1 − F(ρ, |ψ̂⟩⟨ψ̂|) and opt = inf_{|ψ⟩∈G} d_IF(ρ, |ψ⟩⟨ψ|) → infid ρ σ = 1 − Re Σ_i Σ_j ρ_ij σ_ji (Fock-basis series) with σ pure, and optG ρ = ⨅ over the published bosePure n of infid; reason: for pure σ = |ψ⟩⟨ψ|, F(ρ, σ) = ⟨ψ|ρ|ψ⟩ = tr(ρσ), so the values agree on every instance
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Proposition 3.15, printed p. 24 (PDF p. 27); proof on pp. 25–27

import Mathlib
import Definitions.Def_OptGaussTomo_boseGauss
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_vacuum
import Definitions.Def_AgnGaussTomo_Succeeds
import Definitions.Def_AgnGaussTomo_optG

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Proposition 3.15: refinement to `opt + ε` near the vacuum.** Arulandu, Chen, Chen, Li, Ma, *Finding
Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Proposition 3.15,
printed p. 24 (PDF p. 27): "Suppose d_tr(ρ, |0⟩⟨0|) ≤ γ₁, and let opt = inf_{|ψ⟩∈G} d_IF(ρ, |ψ⟩⟨ψ|).
Given ε ∈ (0, 1) and δ ∈ (0, 1/2), there is an algorithm using Õ(n² ε^{-1} log(1/δ)) copies and
single-copy measurements that outputs a pure Gaussian state |ψ̂⟩ satisfying d_IF(ρ, |ψ̂⟩⟨ψ̂|) ≤ opt + ε
with probability at least 1 − δ."

**Formalization Note.** `γ₁` and the constants of `Õ` are universal; `Õ(X)` is
`C·X·log(e + n + 1/ε + 1/δ)^C`. The scheme depends on `n, ε, δ` only. `opt` is `optG ρ`; outputs are
always pure Gaussian states. -/
theorem proposition_3_15 : ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 / 2 →
      ∃ (N : ℕ) (O : Type) (_ : MeasurableSpace O) (S : BosonicLearn.AdaptiveScheme n N O)
        (est : (Fin N → O) → State (Occupation (Fin n))),
        (N : ℝ) ≤ C * (n : ℝ) ^ 2 / ε * Real.log (1 / δ) *
          Real.log (Real.exp 1 + n + 1 / ε + 1 / δ) ^ C ∧
        (∀ x, est x ∈ OptGaussTomo.bosePure n) ∧
        ∀ ρ : State (Occupation (Fin n)),
          BosonicLearn.traceDist ρ.coefficients (vacuum n) ≤ ENNReal.ofReal γ₁ →
          Succeeds S ρ.coefficients
            (fun x => infid ρ.coefficients (est x).coefficients ≤ optG ρ + ε) δ := by sorry

end AgnGaussTomo
