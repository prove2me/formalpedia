-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_105
-- name    : CatalystQLB.Query.eq_105
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:16.5093+00:00
-- url     : https://prove2.me/theorems/c6201283-e22b-4eb2-93d4-6fd5ccf5a041
-- title:
--   Eq. (105) — decision bound $\mathrm{succ}_{\mathrm{dec}}(\gamma)\le4(q-1)(2q_g+1)\sqrt{2^{\ell-\lambda}\|\gamma\|_\infty}$
-- statement:
--   Let an oracle circuit make $q-1\ge0$ queries to $O_f$ and $q_g$ queries to $O_g$, let $\Pi^{\mathrm{dec}}$ be a projector on the $2\lambda+\ell$ qubits, and let $\gamma\succeq0$ with $\mathrm{tr}\,\gamma\le1$. Then
--   $$\mathrm{succ}_{\mathrm{dec}}(\gamma)\le4(q-1)(2q_g+1)\sqrt{2^{\ell-\lambda}\,\|\gamma\|_\infty}.$$
--
--   With $\gamma=|0^\ell\rangle\langle0^\ell|$ it shows that $\ell\le c\lambda$, $c<1$, clean catalyst qubits do not let a circuit distinguish $(x,f(g(x)))$ from $(x,r)$.
--
--   **Formalization Note** $\|\gamma\|_\infty$ is `QAlgorithms.specNorm`.
--
--   Differences from the source:
--   - generalization: Lemma 121's proof (following Lemma 82, “Hence assume $q\ge2$”) → every circuit, including $q=1$; reason: at $q=1$ the right side is $0$ and the advantage is $0$ (p.49: “the two acceptance probabilities are therefore equal”); it specializes to the $q\ge2$ statement
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (105), p.76 (PDF 79)

import Mathlib
import Definitions.Def_CatalystQLB_Query_decisionAdvantage

open scoped ComplexOrder

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (105)**, the decision bound for any catalyst operator (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.4, Lemma 121's proof,
Step (2), p.76 (PDF 79)). For every circuit with `q − 1 = numF C` queries to `O_f` and
`q_g = numG C` to `O_g`, every projector `Pdec` on the `2n + ℓ` qubits and every `0 ⪯ γ` with
`tr γ ≤ 1`: `succ_dec(γ) ≤ 4(q − 1)(2q_g + 1) √(2^{ℓ−n} ‖γ‖_∞)`.

**Formalization Note** `n` is `λ`; `‖γ‖_∞` = `specNorm γ`. Includes `q = 1`, where the advantage
is `0` (p.49: "If `q − 1 = 0`, … the two acceptance probabilities are therefore equal"). -/
theorem eq_105 {n ℓ : ℕ} (C : OracleCircuit n ℓ)
    (Pdec : Matrix (Idx n ℓ) (Idx n ℓ) ℂ) (hP : Pdec.IsHermitian) (hP2 : Pdec * Pdec = Pdec)
    (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (hγ : γ.PosSemidef) (htr : γ.trace.re ≤ 1) :
    decisionAdvantage C Pdec γ ≤ 4 * (C.numF : ℝ) * (2 * (C.numG : ℝ) + 1) *
      Real.sqrt ((2 : ℝ) ^ ((ℓ : ℝ) - n) * specNorm γ) := by sorry

end CatalystQLB.Query
