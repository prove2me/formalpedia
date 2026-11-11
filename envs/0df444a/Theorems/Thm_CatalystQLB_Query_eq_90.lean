-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_90
-- name    : CatalystQLB.Query.eq_90
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:45.857267+00:00
-- url     : https://prove2.me/theorems/5c1938ff-290b-476d-8c45-804df2469926
-- title:
--   Eq. (90) — reversed-problem bound $\mathrm{succ}_{\mathrm{search}}(\gamma)\le q(1+(q-1)(2q_g+1)^2)\,2^{\ell-\lambda}\|\gamma\|_\infty$
-- statement:
--   Let an oracle circuit make $q-1\ge0$ queries to $O_f$ and $q_g$ queries to $O_g$, and let $\gamma\succeq0$ be an operator on the catalyst register with $\mathrm{tr}\,\gamma\le1$. Then
--   $$\mathrm{succ}_{\mathrm{search}}(\gamma)\le q\big(1+(q-1)(2q_g+1)^2\big)\,2^{\ell-\lambda}\,\|\gamma\|_\infty.$$
--   This includes $q=1$, where the circuit makes no query to $f$.
--
--   With $\gamma=|0^\ell\rangle\langle0^\ell|$ it is the pure-catalyst bound Eq. (51): a circuit with $\ell\le c\lambda$, $c<1$, clean catalyst qubits inverts $|x,f(g(x))\rangle\mapsto|x,0^\lambda\rangle$ only with probability $\mathrm{poly}(q)\,2^{-(1-c)\lambda}$.
--
--   **Formalization Note** $q$ is `numF + 1`, $q_g$ is `numG`, $\|\gamma\|_\infty$ is `QAlgorithms.specNorm`.
--
--   Differences from the source:
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (90), p.73 (PDF 76)

import Mathlib
import Definitions.Def_CatalystQLB_Query_searchSuccess

open scoped ComplexOrder

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (90)**, the search bound for any catalyst operator (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.3, Lemma 119's proof, p.73
(PDF 76)). For every circuit with `q − 1 = numF C` queries to `O_f` and `q_g = numG C` queries
to `O_g`, and every `0 ⪯ γ` with `tr γ ≤ 1`:
`succ_search(γ) ≤ q (1 + (q − 1)(2q_g + 1)²) 2^{ℓ−n} ‖γ‖_∞`.
This includes `q = 1` ("For `q = 1`, the circuit makes no queries to `f`. … gives Equation (90)
directly").

**Formalization Note** `n` is `λ`; `q = numF C + 1`; `‖γ‖_∞` = `specNorm γ`; `succ_search` is the
reversed problem (`searchSuccess`). -/
theorem eq_90 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)
    (hγ : γ.PosSemidef) (htr : γ.trace.re ≤ 1) :
    searchSuccess C γ ≤ ((C.numF : ℝ) + 1) * (1 + (C.numF : ℝ) * (2 * (C.numG : ℝ) + 1) ^ 2) *
      (2 : ℝ) ^ ((ℓ : ℝ) - n) * specNorm γ := by sorry

end CatalystQLB.Query
