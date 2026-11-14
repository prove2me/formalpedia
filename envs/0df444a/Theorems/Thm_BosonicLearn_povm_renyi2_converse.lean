-- Prove2me | Theorems.Thm_BosonicLearn_povm_renyi2_converse
-- name    : BosonicLearn.povm_renyi2_converse
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:09:56.356021+00:00
-- url     : https://prove2.me/theorems/adedf2f7-e12b-4fd4-b2c8-b1a6b812bde3
-- title:
--   A Rényi-2 converse for POVM outcome probabilities: $\Pr_\rho(B)^2\le\Pr_\sigma(B)\,\mathrm{Tr}(\rho\sigma^{-1/2}\rho\sigma^{-1/2})$
-- statement:
--   The Cauchy–Schwarz substitute for Fano's inequality and the Holevo bound in the proof of Theorem 9.
--
--   Let $E$ be a POVM on $\ell^2(I)$ ($I$ countable) with a measurable outcome space, $\rho$ a density operator, and $\sigma=\operatorname{diag}(p)$ a diagonal density operator with $p_i>0$. If
--
--   $$q=\sum_{i,j}\frac{|\rho_{ij}|^2}{\sqrt{p_ip_j}}=\operatorname{Tr}\big(\rho\,\sigma^{-1/2}\rho\,\sigma^{-1/2}\big)<\infty,$$
--
--   then for every measurable set $B$ of outcomes $\Pr_\rho(B)^2\le\Pr_\sigma(B)\cdot q$.
--
--   Proof idea: $\operatorname{Tr}(E\rho)=\operatorname{Tr}(\sigma^{1/4}E\sigma^{1/4}\cdot\sigma^{-1/4}\rho\sigma^{-1/4})$, Cauchy–Schwarz for the Hilbert–Schmidt inner product, and $\operatorname{Tr}(\sigma^{1/2}E\sigma^{1/2}E)\le\operatorname{Tr}(\sigma E)$ for $0\preceq E\preceq\mathbf 1$.
--
--   **Formalization Note** The first conclusion records that $\operatorname{diag}(p)$ is a density operator, so that the Born rule of `FockPOVM` applies to it; probabilities are `(E.law · B).toReal`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §8, proof of Theorem 9, pp. 65–67 (Eqs. (229)–(234): Fano's inequality and the Holevo bound, replaced here)

import Mathlib
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open MeasureTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **A Rényi-2 (χ²) converse for POVM outcome probabilities.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §8, proof of Theorem 9, Eqs. (229)–(234), pp. 66–67, where Fano's inequality and the Holevo bound are applied to the
ensemble; this is the Cauchy–Schwarz substitute for that step.

Let `E` be a POVM on `ℓ²(I)`, `ρ` a density operator and `σ = diag(p)` a diagonal density operator with `p_i > 0`.
If `q = ∑_{i,j} |ρ_{ij}|² / √(p_i p_j) = Tr(ρ σ^{−1/2} ρ σ^{−1/2})` is finite, then for every measurable set `B` of
outcomes

`Pr_ρ(B)² ≤ Pr_σ(B) · q`.

**Formalization Note.** `Tr(E ρ) = Tr(σ^{1/4} E σ^{1/4} · σ^{−1/4} ρ σ^{−1/4})`, Cauchy–Schwarz for the Hilbert–Schmidt
inner product, and `Tr(σ^{1/2} E σ^{1/2} E) ≤ Tr(σ E)` for `0 ⪯ E ⪯ 1`. The first conclusion records that `diag(p)` is a
density operator, so that the Born rule of `E` applies to it. -/
theorem povm_renyi2_converse {I O : Type} [DecidableEq I] [Countable I] [MeasurableSpace O]
    (E : FockPOVM I O) (ρ : Matrix I I ℂ) (hρ : IsDensity ρ)
    (p : I → ℝ) (hp : ∀ i, 0 < p i) (hp1 : HasSum p 1)
    (q : ℝ) (hq : HasSum (fun x : I × I => ‖ρ x.1 x.2‖ ^ 2 / Real.sqrt (p x.1 * p x.2)) q)
    (B : Set O) (hB : MeasurableSet B) :
    IsDensity (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) ∧
    (E.law ρ B).toReal ^ 2 ≤ (E.law (Matrix.diagonal fun i => ((p i : ℝ) : ℂ)) B).toReal * q := by sorry

end BosonicLearn
