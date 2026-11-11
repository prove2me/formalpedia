-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_85
-- name    : CatalystQLB.Query.eq_85
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:05.34728+00:00
-- url     : https://prove2.me/theorems/42e625bb-7854-45d9-b919-0fbcdb616b54
-- title:
--   Eq. (85) — rank and averaging bound $\mathbb E\,\mathrm{tr}[M(|x,f(g(x))\rangle\langle\cdot|\otimes\gamma)]\le2^{\ell-\lambda}\|\gamma\|_\infty$
-- statement:
--   Let an oracle circuit make $q-1$ queries to $O_f$, let $M=Z_q^\dagger\,\Pi^{\mathrm{search}}_x\,Z_q$, and let $\gamma\succeq0$ be an operator on the catalyst register with $\mathrm{tr}\,\gamma\le1$. Then
--   $$\mathbb E\,\mathrm{tr}\big[M(|x,f(g(x))\rangle\langle x,f(g(x))|\otimes\gamma)\big]=2^{-\lambda}\,\mathbb E\,\mathrm{tr}\big[M(|x\rangle\langle x|\otimes I_R\otimes\gamma)\big]\le2^{-\lambda}\|\gamma\|_\infty\,\mathbb E\,\mathrm{tr}[M]\le2^{\ell-\lambda}\|\gamma\|_\infty,$$
--   where all expectations are over $f,g,x$.
--
--   The equality averages over the uniform value $f(g(x))$, of which $M$ is independent; the last step uses $\mathrm{tr}\,M\le\mathrm{rank}\,M\le2^\ell$. This bounds the branch on which $f$ is never queried at $g(x)$.
--
--   **Formalization Note** $\|\gamma\|_\infty$ is the operator norm `QAlgorithms.specNorm`.
--
--   Differences from the source:
--   - generalization: the proof's “Assume for now that $q\ge2$” → every circuit, $q\ge1$; reason: at $q=1$, $Z_q=U$, which is exactly the case $M=U^\dagger\Pi^{\mathrm{search}}U$ the paper applies on p.73; it specializes to the $q\ge2$ statement
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (85), p.72 (PDF 75); Eq. (45), p.45 (PDF 48)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_branchZ
import Definitions.Def_CatalystQLB_Query_searchProj
import Definitions.Def_CatalystQLB_Query_expectFGX

open scoped Matrix ComplexOrder

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (85)**, the rank/averaging bound (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.3, Lemma 119's proof, Step (1), p.72
(PDF 75); the case `γ = |0^ℓ⟩⟨0^ℓ|` is Eq. (45), p.45). Let `q − 1 = numF C`,
`M = Z_q† Π^search Z_q` and `γ ⪰ 0` on `C` with `tr γ ≤ 1`. Then
`E tr[M(|x, f(g(x))⟩⟨x, f(g(x))| ⊗ γ)] = 2^{−n} E tr[M(|x⟩⟨x| ⊗ I_R ⊗ γ)]
  ≤ 2^{−n} ‖γ‖_∞ E tr[M] ≤ 2^{ℓ−n} ‖γ‖_∞`.

**Formalization Note** `n` is `λ`; expectations over `f, g, x` (`expectFGX`); real parts of the
traces; `‖γ‖_∞` = `specNorm γ`. Stated for every circuit: at `q = 1`, `Z_q = U`, the case the
paper uses on p.73 ("with `M = U†Π^search U`"). -/
theorem eq_85 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ)
    (hγ : γ.PosSemidef) (htr : γ.trace.re ≤ 1) :
    expectFGX n (fun f g x => (Matrix.trace
        ((C.branchZ f g x (C.numF + 1))ᴴ * searchProj x * C.branchZ f g x (C.numF + 1) *
          Matrix.kronecker (Matrix.single (x, f (g x)) (x, f (g x)) (1 : ℂ)) γ)).re) =
      ((2 : ℝ) ^ n)⁻¹ * expectFGX n (fun f g x => (Matrix.trace
        ((C.branchZ f g x (C.numF + 1))ᴴ * searchProj x * C.branchZ f g x (C.numF + 1) *
          Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
            (1 : Matrix (Qubits n) (Qubits n) ℂ)) γ)).re) ∧
    ((2 : ℝ) ^ n)⁻¹ * expectFGX n (fun f g x => (Matrix.trace
        ((C.branchZ f g x (C.numF + 1))ᴴ * searchProj x * C.branchZ f g x (C.numF + 1) *
          Matrix.kronecker (Matrix.kronecker (Matrix.single x x (1 : ℂ))
            (1 : Matrix (Qubits n) (Qubits n) ℂ)) γ)).re) ≤
      ((2 : ℝ) ^ n)⁻¹ * specNorm γ * expectFGX n (fun f g x => (Matrix.trace
        ((C.branchZ f g x (C.numF + 1))ᴴ * searchProj x * C.branchZ f g x (C.numF + 1))).re) ∧
    ((2 : ℝ) ^ n)⁻¹ * specNorm γ * expectFGX n (fun f g x => (Matrix.trace
        ((C.branchZ f g x (C.numF + 1))ᴴ * searchProj x * C.branchZ f g x (C.numF + 1))).re) ≤
      (2 : ℝ) ^ ((ℓ : ℝ) - n) * specNorm γ := by sorry

end CatalystQLB.Query
