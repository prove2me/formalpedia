-- Prove2me | Theorems.Thm_CatalystQLB_Query_Supplement_theorem_144
-- name    : CatalystQLB.Query.Supplement.theorem_144
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:05:51.751179+00:00
-- url     : https://prove2.me/theorems/82cba86a-4d4a-41d8-a6df-b34c9a1c7ffa
-- title:
--   Theorem 144 — a catalyst Hamiltonian changes catalytic work extraction by at most $L(H_C)\,\varepsilon$
-- statement:
--   Let $L(H)=\lambda_{\max}(H)-\lambda_{\min}(H)$ denote the spectral width and $H^{\mathrm{tot}}=H\otimes I_C+I_{\mathrm{IO}}\otimes H_C$. The following hold.
--
--   1. For all $\rho\in\mathrm{Den}(n)$, $H\in\mathrm{Herm}(n)$, $\eta\in\mathrm{Den}(\ell)$, $H_C\in\mathrm{Herm}(\ell)$ and $\varepsilon\ge0$,
--   $$\Big|\mathsf{cat}\text{-}\mathrm{erg}^\varepsilon_{\rho,H}[\eta,H_C]-\mathsf{cat}\text{-}\mathrm{erg}^\varepsilon_{\rho,H}[\eta,0]\Big|\le L(H_C)\,\varepsilon ;$$
--   in particular the two quantities are equal when $\varepsilon=0$.
--   2. For every admissible extractor $\mathcal A$ and every $\lambda$: if every circuit $U_\lambda$ that $\mathcal A$ generates (for every instance $(\rho,H,O)$ and every outcome of its internal randomness) lies in $\mathsf{cat}\text{-}\mathcal U_{\eta_\lambda}(n,\ell,\varepsilon_{\mathcal A}(\lambda))$, then
--   $$\Big|\mathbb E_{\mathcal D}\mathcal W^{(\ell)}_{\rho,H,\mathcal A}[\eta,H_C](\lambda)-\mathbb E_{\mathcal D}\mathcal W^{(\ell)}_{\rho,H,\mathcal A}[\eta,0](\lambda)\Big|\le L(H_{C,\lambda})\,\varepsilon_{\mathcal A}(\lambda)=:\nu_{\mathcal A}(\lambda).$$
--   3. If $L(H_{C,\lambda})$ is polynomially bounded in $\lambda$ (and $\varepsilon_{\mathcal A}$ is negligible, as admissibility requires), then $\nu_{\mathcal A}$ is negligible.
--
--   Giving the catalyst its own energy therefore changes neither the information-theoretic catalytic ergotropy beyond $L(H_C)\varepsilon$ nor the work of any efficient catalytic extractor beyond a negligible amount, as long as the catalyst Hamiltonian has polynomially bounded spectral width.
--
--   **Formalization Note** Part 2 is stated for one $\lambda$ on an arbitrary probability space $(\Omega,\mu)$ that carries the joint law of the instance $(\rho,H,O)\leftarrow\mathcal D$ and the extractor's randomness, with $\rho(\omega)\in\mathrm{Den}(n)$, $H(\omega)\in\mathrm{Herm}(n)$ and generated circuit $U(\omega)\in\mathsf{cat}\text{-}\mathcal U_\eta(n,\ell,\varepsilon)$ for every $\omega$; the two work integrands are assumed integrable, as the paper's expectations are real numbers. "Negligible" is the published `PPADSIS.SubexpSIS.Negligible` (nonnegative and eventually below $\lambda^{-c}$ for every $c>0$); "polynomially bounded" is $L(H_{C,\lambda})\le C\lambda^k$ for all large $\lambda$.
--
--   Differences from the source:
--   - generalization: every admissible PPT oracle extractor A and the distribution D over triples (ρ, H, O) → every probability space (Ω, μ) with maps ω ↦ (ρ, H, U) whose circuits all lie in cat-U_η(n, ℓ, ε); reason: an admissible PPT extractor run on (ρ, H, O) ← D induces such a space (joint law of instance and internal randomness), so the Lean statement specializes to the paper's for any formalization of PPT
--   - encoding: E_D E_A of real-valued work → Bochner integral over μ, with both work integrands assumed integrable; reason: the paper's expectations are finite real numbers; the hypothesis excludes only undefined expectations
--   - reading: L(H_{C,λ}) polynomially bounded in λ; negl(λ) grows slower than 1/p(λ) for every polynomial p → ∃ C k, eventually L(H_{C,λ}) ≤ C·λ^k; PPADSIS.SubexpSIS.Negligible (ν ≥ 0 and ∀ c > 0, eventually ν(λ) ≤ λ^{−c}); reason: standard definitions of the paper's informal terms; ε_A is a trace-distance bound, hence nonnegative whenever an admissible circuit exists
--   - encoding: 'in particular, equal when ε = 0' → an extra conjunct ε = 0 → equality; reason: implied by the inequality; stated as in the paper
--   - generalization: ν_A(λ) = L(H_{C,λ}) ε_A(λ) for the negligible error ε_A of an admissible extractor, with ℓ polynomially bounded and polynomial-time computable → every family ℓ : ℕ → ℕ, every family of Hermitian H_{C,λ} and every negligible ε_A : ℕ → ℝ; reason: admissibility (Definition 142) makes ε_A negligible, so the paper's ν_A is an instance; the asymptotic sentence uses nothing else about A or ℓ
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Theorem 144, Eqs. (177)–(178), p.97 (PDF 100); Definitions 141–142, Eqs. (175)–(176), p.96 (PDF 99)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_PPADSIS_SubexpSIS_Negligible
import Definitions.Def_CatalystQLB_Query_Supplement_spectralWidth
import Definitions.Def_CatalystQLB_Query_Supplement_IsApproxCatalytic
import Definitions.Def_CatalystQLB_Query_Supplement_extractedWork
import Definitions.Def_CatalystQLB_Query_Supplement_expectedWork
import Definitions.Def_CatalystQLB_Query_Supplement_catErgHC

open scoped Matrix Kronecker
open MeasureTheory Filter

namespace CatalystQLB.Query.Supplement

open QAlgorithms

/-- **Theorem 144** (The catalyst Hamiltonian does not change catalytic work extraction; Arora,
Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of
Catalysts*, arXiv:2609.40323 (version of 2026-11-03), Theorem 144, Eqs. (177)–(178), p.97
(PDF 100); Definitions 141–142, p.96 (PDF 99)). The three conjuncts are:

1. (Eq. (177)) For all `ρ ∈ Den(n)`, `H ∈ Herm(n)`, `η ∈ Den(ℓ)`, `H_C ∈ Herm(ℓ)` and `ε ≥ 0`,
   `|cat-erg^ε_{ρ,H}[η, H_C] − cat-erg^ε_{ρ,H}[η, 0]| ≤ L(H_C) ε`; in particular the two are
   equal when `ε = 0`.
2. (Eq. (178)) For every admissible extractor and every `λ`: if every generated circuit lies in
   `cat-U_η(n, ℓ, ε)`, the `D`-averaged work with catalyst Hamiltonian `H_C` and with `0` differ by
   at most `L(H_C) ε`. Here one probability space `(Ω, μ)` carries the joint law of
   `(ρ, H, O) ← D` and of the extractor's randomness; `ρ ω ∈ Den(n)`, `H ω ∈ Herm(n)` and the
   generated circuit `U ω ∈ cat-U_η(n, ℓ, ε)` for every outcome `ω`.
3. If `L(H_{C,λ})` is polynomially bounded in `λ` and `ε_A` is negligible, then
   `ν_A(λ) := L(H_{C,λ}) ε_A(λ)` is negligible.

**Formalization Note** Part 2 is stated for an arbitrary probability space and arbitrary maps
`ω ↦ (ρ, H, U)`, which every admissible PPT extractor with oracle access and every `D` induce;
this covers the paper's statement for any formalization of "PPT". The paper's expectations are
real numbers, so the two work integrands are assumed integrable. "Polynomially bounded" is
`∃ C k, L(H_{C,λ}) ≤ C λ^k` for all large `λ`; "negligible" is the published
`PPADSIS.SubexpSIS.Negligible`. `n = n(λ)` and `ℓ = ℓ(λ)` are fixed in part 2 (one `λ`); the
family in part 3 has `ℓ : ℕ → ℕ`. -/
theorem theorem_144 :
    (∀ (n ℓ : ℕ) (ρ H : Matrix (Qubits n) (Qubits n) ℂ) (η HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)
        (ε : ℝ), WildeQIT.IsDensityOperator ρ → H.IsHermitian → WildeQIT.IsDensityOperator η →
        ∀ hHC : HC.IsHermitian, 0 ≤ ε →
          |catErgHC ρ H η HC ε - catErgHC ρ H η 0 ε| ≤ spectralWidth HC hHC * ε ∧
          (ε = 0 → catErgHC ρ H η HC ε = catErgHC ρ H η 0 ε)) ∧
    (∀ (n ℓ : ℕ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ρ H : Ω → Matrix (Qubits n) (Qubits n) ℂ)
        (U : Ω → Matrix.unitaryGroup (Qubits n × Qubits ℓ) ℂ)
        (η HC : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (ε : ℝ),
        (∀ ω, WildeQIT.IsDensityOperator (ρ ω)) → (∀ ω, (H ω).IsHermitian) →
        WildeQIT.IsDensityOperator η → ∀ hHC : HC.IsHermitian,
        (∀ ω, IsApproxCatalytic (U ω) η ε) →
        Integrable (fun ω => extractedWork (ρ ω) (H ω) η HC (U ω)) μ →
        Integrable (fun ω => extractedWork (ρ ω) (H ω) η 0 (U ω)) μ →
          |expectedWork μ ρ H U η HC - expectedWork μ ρ H U η 0| ≤ spectralWidth HC hHC * ε) ∧
    (∀ (ℓ : ℕ → ℕ) (HC : ∀ lam, Matrix (Qubits (ℓ lam)) (Qubits (ℓ lam)) ℂ)
        (hHC : ∀ lam, (HC lam).IsHermitian) (εA : ℕ → ℝ),
        PPADSIS.SubexpSIS.Negligible εA →
        (∃ C : ℝ, ∃ k : ℕ, ∀ᶠ lam in atTop, spectralWidth (HC lam) (hHC lam) ≤ C * (lam : ℝ) ^ k) →
          PPADSIS.SubexpSIS.Negligible (fun lam => spectralWidth (HC lam) (hHC lam) * εA lam)) := by sorry

end CatalystQLB.Query.Supplement
