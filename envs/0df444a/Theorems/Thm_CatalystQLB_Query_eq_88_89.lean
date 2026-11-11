-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_88_89
-- name    : CatalystQLB.Query.eq_88_89
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:23.060542+00:00
-- url     : https://prove2.me/theorems/968a0c82-8435-482e-b858-da44d37c1c5c
-- title:
--   Eqs. (88)–(89) — branch weights $\sum_ib_i\le(q-1)(2q_g+1)^2\,2^{\ell-\lambda}\|\gamma\|_\infty$
-- statement:
--   Let an oracle circuit make $q-1\ge1$ queries to $O_f$ and $q_g$ queries to $O_g$, let $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$, and let $\gamma\succeq0$ with $\mathrm{tr}\,\gamma\le1$. Then for every $1\le i\le q-1$ (Eq. (88))
--   $$b_i=2^{-\lambda}\,\mathbb E\,\mathrm{tr}\big[(|x\rangle\langle x|\otimes I_R\otimes\gamma)Z_i^\dagger\Pi Z_i\big]\le2^{-\lambda}\|\gamma\|_\infty\,\mathbb E\,\mathrm{tr}\big[(|x\rangle\langle x|\otimes I_{RC})Z_i^\dagger\Pi Z_i\big],$$
--   and (Eq. (89))
--   $$\sum_{i=1}^{q-1}b_i\le(q-1)(2q_g+1)^2\,2^{\ell-\lambda}\,\|\gamma\|_\infty.$$
--
--   The total weight of the branches that query $f$ at $g(x)$ is controlled through the inverter of Eq. (48) and the inversion bound Eq. (50).
--
--   **Formalization Note** $\|\gamma\|_\infty$ is `QAlgorithms.specNorm`.
--
--   Differences from the source:
--   - encoding: the chain (89) with the middle member $(q-1)2^\ell\|\gamma\|_\infty\,\mathrm{succ}_{\mathrm{inv}}$ → its first and last members; reason: the middle member names the inverter of Eq. (48), a separate milestone; the stated inequality is the chain's conclusion
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eqs. (88)–(89), p.73 (PDF 76)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_bTerm

open scoped Matrix ComplexOrder

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eqs. (88)–(89)**, the branch weights (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.3, Lemma 119's proof, Step (2), p.73
(PDF 76)). Let `q − 1 = numF C ≥ 1`, `q_g = numG C`, `Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC`, and
`0 ⪯ γ` with `tr γ ≤ 1`. Then for every `1 ≤ i ≤ q − 1`
`b_i = 2^{−n} E tr[(|x⟩⟨x| ⊗ I_R ⊗ γ) Z_i† Π Z_i] ≤ 2^{−n} ‖γ‖_∞ E tr[(|x⟩⟨x| ⊗ I_RC) Z_i† Π Z_i]`
(Eq. (88)), and `Σ_{i=1}^{q−1} b_i ≤ (q − 1)(2q_g + 1)² 2^{ℓ−n} ‖γ‖_∞` (Eq. (89)).

**Formalization Note** `n` is `λ`; `‖γ‖_∞` = `specNorm γ`; real parts of traces. The middle
member `(q−1)2^ℓ‖γ‖_∞ succ_inv` of Eq. (89) refers to the inverter of Eq. (48) and is left out. -/
theorem eq_88_89 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (hq : 1 ≤ C.numF)
    (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (hγ : γ.PosSemidef) (htr : γ.trace.re ≤ 1) :
    (∀ i ∈ Finset.Icc 1 C.numF,
      C.bTerm γ i = ((2 : ℝ) ^ n)⁻¹ * expectFGX n (fun f g x => (Matrix.trace
          (Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
              (1 : Matrix (Qubits n) (Qubits n) ℂ)) γ *
            (C.branchZ f g x i)ᴴ * firstQueryProj (g x) * C.branchZ f g x i)).re) ∧
      ((2 : ℝ) ^ n)⁻¹ * expectFGX n (fun f g x => (Matrix.trace
          (Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
              (1 : Matrix (Qubits n) (Qubits n) ℂ)) γ *
            (C.branchZ f g x i)ᴴ * firstQueryProj (g x) * C.branchZ f g x i)).re) ≤
        ((2 : ℝ) ^ n)⁻¹ * specNorm γ * expectFGX n (fun f g x => (Matrix.trace
          (Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
              (1 : Matrix (Qubits n) (Qubits n) ℂ)) (1 : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) *
            (C.branchZ f g x i)ᴴ * firstQueryProj (g x) * C.branchZ f g x i)).re)) ∧
    ∑ i ∈ Finset.Icc 1 C.numF, C.bTerm γ i ≤
      (C.numF : ℝ) * (2 * (C.numG : ℝ) + 1) ^ 2 * (2 : ℝ) ^ ((ℓ : ℝ) - n) *
        specNorm γ := by sorry

end CatalystQLB.Query
