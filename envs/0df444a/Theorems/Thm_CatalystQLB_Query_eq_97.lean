-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_97
-- name    : CatalystQLB.Query.eq_97
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:45.559548+00:00
-- url     : https://prove2.me/theorems/5a1707c4-aa5e-4e67-9272-21305e37553b
-- title:
--   Eq. (97) — reversed-problem bound for the catalyst $\eta_{\ell,p}$
-- statement:
--   Let $0<p<1/2$ and $\delta>0$. For every $\ell$ and every oracle circuit making $q-1\ge0$ queries to $O_f$ and $q_g$ queries to $O_g$,
--   $$\mathrm{succ}_{\mathrm{search}}(\eta_{\ell,p})\le q\big(1+(q-1)(2q_g+1)^2\big)\,2^{\ell(1-h_2(p)+\delta)-\lambda}+\exp\!\Big(-\frac{2\ell\delta^2}{\log_2^2((1-p)/p)}\Big).$$
--
--   When $c(1-h_2(p)+\delta)<1$ and $\ell\le c\lambda$, both terms are exponentially small in $\lambda$ for polynomially many queries (Eqs. (98)–(99)), which is the search half of the mixed-catalyst lower bound.
--
--   **Formalization Note** $h_2$ in bits; the power of $2$ is a real power.
--
--   Differences from the source:
--   - generalization: $\delta$ chosen with $0<\delta<h_2(p)$ and $c(1-h_2(p)+\delta)<1$ → every $\delta>0$; reason: the derivation uses only $\delta>0$; it specializes to the paper's choice
--   - encoding: the chain (97) with the middle member $q(1+(q-1)(2q_g+1)^2)2^{\ell-\lambda}\|\gamma\|_\infty+\mathrm{tr}(\eta_\lambda-\gamma)$ → its first and last members; reason: the middle member involves the cutoff $\gamma$, which the stated bound does not need
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (97), p.75 (PDF 78)

import Mathlib
import Definitions.Def_CatalystQLB_Query_searchSuccess
import Definitions.Def_CatalystQLB_Query_catalystState
import Definitions.Def_WildeQIT_binaryEntropy

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (97)**, the search bound for the catalyst `η_{ℓ,p}` (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.3, Lemma 119's proof,
p.75 (PDF 78)). Let `0 < p < 1/2` and `δ > 0`. For every `ℓ` and every circuit with
`q − 1 = numF C` queries to `O_f` and `q_g = numG C` to `O_g`:
`succ_search(η_{ℓ,p}) ≤ q (1 + (q − 1)(2q_g + 1)²) 2^{ℓ(1−h₂(p)+δ)−n} + exp(−2ℓδ² / log₂²((1 − p)/p))`.

**Formalization Note** `n` is `λ`; `q = numF C + 1`; `h₂` in bits; real exponent (`Real.rpow`).
The paper chooses `0 < δ < h₂(p)` with `c(1 − h₂(p) + δ) < 1`; the statement holds for every
`δ > 0`. The middle member of Eq. (97) (with the cutoff `γ`) is left out. -/
theorem eq_97 {n ℓ : ℕ} {p δ : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hδ : 0 < δ)
    (C : OracleCircuit n ℓ) :
    searchSuccess C (catalystState ℓ p) ≤
      ((C.numF : ℝ) + 1) * (1 + (C.numF : ℝ) * (2 * (C.numG : ℝ) + 1) ^ 2) *
        (2 : ℝ) ^ ((ℓ : ℝ) * (1 - WildeQIT.binaryEntropy p + δ) - n) +
      Real.exp (-(2 * (ℓ : ℝ) * δ ^ 2 / (Real.logb 2 ((1 - p) / p)) ^ 2)) := by sorry

end CatalystQLB.Query
