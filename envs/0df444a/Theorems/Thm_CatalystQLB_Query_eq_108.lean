-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_108
-- name    : CatalystQLB.Query.eq_108
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:22.637896+00:00
-- url     : https://prove2.me/theorems/898c297c-c478-467f-83e0-d6506afcc476
-- title:
--   Eq. (108) — decision bound for the catalyst $\eta_{\ell,p}$
-- statement:
--   Let $0<p<1/2$ and $\delta>0$. For every $\ell$, every oracle circuit making $q-1\ge0$ queries to $O_f$ and $q_g$ queries to $O_g$, and every projector $\Pi^{\mathrm{dec}}$ on the $2\lambda+\ell$ qubits,
--   $$\mathrm{succ}_{\mathrm{dec}}(\eta_{\ell,p})\le4(q-1)(2q_g+1)\,2^{[\ell(1-h_2(p)+\delta)-\lambda]/2}+\exp\!\Big(-\frac{2\ell\delta^2}{\log_2^2((1-p)/p)}\Big).$$
--
--   This is the decision half of the mixed-catalyst lower bound.
--
--   **Formalization Note** $h_2$ in bits; the power of $2$ is a real power.
--
--   Differences from the source:
--   - generalization: $\delta$ chosen with $0<\delta<h_2(p)$ and $c(1-h_2(p)+\delta)<1$ → every $\delta>0$; reason: the derivation uses only $\delta>0$; it specializes to the paper's choice
--   - encoding: the chain (107)–(108) through $\mathrm{succ}_{\mathrm{dec}}(\gamma)+\mathrm{tr}(\eta_\lambda-\gamma)$ → its first and last members; reason: the middle members involve the cutoff $\gamma$, which the stated bound does not need
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (108), p.76 (PDF 79)

import Mathlib
import Definitions.Def_CatalystQLB_Query_decisionAdvantage
import Definitions.Def_CatalystQLB_Query_catalystState
import Definitions.Def_WildeQIT_binaryEntropy

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (108)**, the decision bound for the catalyst `η_{ℓ,p}` (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.4, Lemma 121's proof,
p.76 (PDF 79)). Let `0 < p < 1/2` and `δ > 0`. For every `ℓ`, every circuit with
`q − 1 = numF C` queries to `O_f` and `q_g = numG C` to `O_g`, and every projector `Pdec` on
the `2n + ℓ` qubits:
`succ_dec(η_{ℓ,p}) ≤ 4(q − 1)(2q_g + 1) 2^{[ℓ(1−h₂(p)+δ)−n]/2} + exp(−2ℓδ² / log₂²((1 − p)/p))`.

**Formalization Note** `n` is `λ`; `h₂` in bits; real exponent. The paper chooses
`0 < δ < h₂(p)` with `c(1 − h₂(p) + δ) < 1`; the statement holds for every `δ > 0`. The
members of Eq. (107) (with the cutoff `γ`) are left out. -/
theorem eq_108 {n ℓ : ℕ} {p δ : ℝ} (hp0 : 0 < p) (hp : p < 1 / 2) (hδ : 0 < δ)
    (C : OracleCircuit n ℓ)
    (Pdec : Matrix (Idx n ℓ) (Idx n ℓ) ℂ) (hP : Pdec.IsHermitian) (hP2 : Pdec * Pdec = Pdec) :
    decisionAdvantage C Pdec (catalystState ℓ p) ≤
      4 * (C.numF : ℝ) * (2 * (C.numG : ℝ) + 1) *
        (2 : ℝ) ^ (((ℓ : ℝ) * (1 - WildeQIT.binaryEntropy p + δ) - n) / 2) +
      Real.exp (-(2 * (ℓ : ℝ) * δ ^ 2 / (Real.logb 2 ((1 - p) / p)) ^ 2)) := by sorry

end CatalystQLB.Query
