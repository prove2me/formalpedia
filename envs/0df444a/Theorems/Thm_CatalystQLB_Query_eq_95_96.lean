-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_95_96
-- name    : CatalystQLB.Query.eq_95_96
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:22:24.984122+00:00
-- url     : https://prove2.me/theorems/c53196e8-85e5-44b9-a135-b6676fd8bdfd
-- title:
--   Eqs. (95)–(96) — spectral cutoff of $\eta_{\ell,p}$ and its Hoeffding tail
-- statement:
--   Let $0<p<1/2$, $\delta>0$, $\ell\in\mathbb N$, and let $\gamma$ be the spectral cutoff of $\eta_{\ell,p}$ (Eq. (95)). Then
--   1. $0\preceq\gamma\preceq\eta_{\ell,p}$ and $\mathrm{tr}\,\gamma\le1$;
--   2. $\|\gamma\|_\infty\le2^{-\ell(h_2(p)-\delta)}$;
--   3. the excluded weight satisfies (Eq. (96))
--   $$\mathrm{tr}[\eta_{\ell,p}-\gamma]\le\exp\!\Big(-\frac{2\ell\delta^2}{\log_2^2((1-p)/p)}\Big).$$
--
--   The tail bound is Hoeffding's inequality for the Hamming weight of $\ell$ independent Bernoulli($p$) bits, since $I_\ell(z)-\ell h_2(p)=(\mathrm{hw}(z)-\ell p)\log_2\frac{1-p}{p}$. Together with the bounds for a general $\gamma$ it handles mixed catalysts.
--
--   **Formalization Note** $h_2$ is `WildeQIT.binaryEntropy` (bits), $\|\cdot\|_\infty$ is `QAlgorithms.specNorm`; traces are real parts.
--
--   Differences from the source:
--   - generalization: $\delta$ chosen with $0<\delta<h_2(p)$ and $c(1-h_2(p)+\delta)<1$ → every $\delta>0$; reason: the derivation uses only $\delta>0$; it specializes to the paper's choice
--   - encoding: the chain (96) through $\Pr_{z\sim\mu_p}[\cdot]$ → its first and last members; reason: the middle members are the probability of the excluded strings written two ways
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eqs. (95)–(96), p.74 (PDF 77)

import Mathlib
import Definitions.Def_CatalystQLB_Query_catalystState
import Definitions.Def_CatalystQLB_Query_cutoffState

open scoped ComplexOrder

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eqs. (95)–(96)**, the spectral cutoff (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.3, Lemma 119's proof, p.74 (PDF 77)). Let
`0 < p < 1/2`, `δ > 0`, and `γ` the cutoff of `η_{ℓ,p}` (Eq. (95)). Then
1. `0 ⪯ γ ⪯ η_{ℓ,p}` and `tr γ ≤ 1`;
2. `‖γ‖_∞ ≤ 2^{−ℓ(h₂(p)−δ)}`;
3. `tr[η_{ℓ,p} − γ] ≤ exp(−2ℓδ² / log₂²((1 − p)/p))` (Eq. (96), by Hoeffding's inequality).

**Formalization Note** `h₂` = `WildeQIT.binaryEntropy` (bits); `log₂` = `Real.logb 2`;
`‖·‖_∞` = `specNorm`; real parts of traces. The paper chooses `0 < δ < h₂(p)` with
`c(1 − h₂(p) + δ) < 1`; the statement holds for every `δ > 0`. -/
theorem eq_95_96 {p δ : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hδ : 0 < δ) (ℓ : ℕ) :
    (cutoffState ℓ p δ).PosSemidef ∧ (catalystState ℓ p - cutoffState ℓ p δ).PosSemidef ∧
    (cutoffState ℓ p δ).trace.re ≤ 1 ∧
    specNorm (cutoffState ℓ p δ) ≤ (2 : ℝ) ^ (-((ℓ : ℝ) * (WildeQIT.binaryEntropy p - δ))) ∧
    (catalystState ℓ p - cutoffState ℓ p δ).trace.re ≤
      Real.exp (-(2 * (ℓ : ℝ) * δ ^ 2 / (Real.logb 2 ((1 - p) / p)) ^ 2)) := by sorry

end CatalystQLB.Query
