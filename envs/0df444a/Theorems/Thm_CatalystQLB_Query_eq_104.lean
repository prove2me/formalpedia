-- Prove2me | Theorems.Thm_CatalystQLB_Query_eq_104
-- name    : CatalystQLB.Query.eq_104
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:54.775968+00:00
-- url     : https://prove2.me/theorems/e4d1ab4a-0629-445e-9c46-4d05f26c189b
-- title:
--   Eq. (104) — decision bound, Step (1): $\mathrm{succ}_{\mathrm{dec}}(\gamma)\le4\sqrt{(q-1)\sum_ib_i}$
-- statement:
--   Let an oracle circuit make $q-1\ge1$ queries to $O_f$, let $\Pi^{\mathrm{dec}}$ be a projector on the $2\lambda+\ell$ qubits, $\Pi=|g(x)\rangle\langle g(x)|_Q\otimes I_{RC}$, and let $|\chi_\gamma\rangle\in C\otimes C'$ be a purification of $\gamma=\mathrm{tr}_{C'}|\chi_\gamma\rangle\langle\chi_\gamma|$ with $\mathrm{tr}\,\gamma\le1$. Then
--   $$\mathrm{succ}_{\mathrm{dec}}(\gamma)\le4\sum_{i=1}^{q-1}\mathbb E\,\big\|\Pi Z_i\big(|x,f(g(x))\rangle\otimes|\chi_\gamma\rangle\big)\big\|\le4\sqrt{(q-1)\sum_{i=1}^{q-1}b_i}.$$
--
--   The branch on which $f$ is never queried at $g(x)$ cannot tell $f(g(x))$ from a uniform $r$, so only the branch weights $b_i$ contribute to the advantage.
--
--   **Formalization Note** $C'$ is any finite purifying system and $\Pi Z_i$ acts as $\Pi Z_i\otimes I_{C'}$. The vector $|x,f(g(x))\rangle\otimes|\chi_\gamma\rangle$ has amplitude $\chi(c,c')$ at $((x,f(g(x)),c),c')$.
--
--   Differences from the source:
--   - encoding: “a purification $|\chi_\gamma\rangle$ of $\gamma$” → any vector $\chi$ on $C\times C'$ ($C'$ a finite type) with $\gamma_{cd}=\sum_e\chi(c,e)\overline{\chi(d,e)}$; operators act as $\cdot\otimes I_{C'}$; reason: the definition of a purification
--   - encoding: the five-member chain (104) → its first and last inequalities; reason: the omitted members are the Cauchy–Schwarz steps and $\mathbb E\|\cdot\|^2=b_i$; the stated relations are the chain's first step and its conclusion
--   - generalization: the proof's standing $\ell=\ell(\lambda)=\lfloor c\lambda\rfloor$ → every $\ell\in\mathbb N$ and every $\lambda$; reason: the display is explicit in $\ell$ and $\lambda$ and its derivation never uses the relation between them; it specializes to the source's $\ell(\lambda)$
--   - encoding: $\mathbb E_{f,g,x}$ and $\mathrm{tr}[\cdot]$ of positive operators → normalized finite sums (`expectFGX`) and the real part of the matrix trace; reason: Lean convention; for the positive operators to which the source applies the formulas the trace is real, so no instance changes
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), Eq. (104), p.76 (PDF 79); Eqs. (54), (58)–(64), pp.50–51 (PDF 53–54)

import Mathlib
import Definitions.Def_CatalystQLB_Query_decisionAdvantage
import Definitions.Def_CatalystQLB_Query_OracleCircuit_bTerm

open scoped Matrix

namespace CatalystQLB.Query

open QAlgorithms

/-- **Eq. (104)**, Step (1) of the decision bound (arXiv:2609.40323 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, version of 2026-11-03), §9.4, Lemma 121's proof, p.76 (PDF 79);
the pure case is Eq. (54) with Eqs. (58)–(64), pp.50–51). Let `q − 1 = numF C ≥ 1`, let
`Pdec` be a projector on the `2n + ℓ` qubits, `Π = |g(x)⟩⟨g(x)|_Q ⊗ I_RC`, and let
`|χ_γ⟩ ∈ C ⊗ C'` be a purification of `γ = tr_{C'} |χ_γ⟩⟨χ_γ|` with `tr γ ≤ 1`. Then
`succ_dec(γ) ≤ 4 Σ_{i=1}^{q−1} E ‖Π Z_i (|x, f(g(x))⟩ ⊗ |χ_γ⟩)‖ ≤ 4 √((q − 1) Σ_{i=1}^{q−1} b_i)`.

**Formalization Note** `n` is `λ`; `C'` is any finite purifying system; `Π Z_i` acts as
`Π Z_i ⊗ I_{C'}`. The vector `|x, f(g(x))⟩ ⊗ |χ_γ⟩` has entry `χ(c, c')` at `((x, f(g(x)), c), c')`
and `0` elsewhere. The intermediate members of Eq. (104) (Cauchy–Schwarz steps) are left out. -/
theorem eq_104 {n ℓ : ℕ} (C : OracleCircuit n ℓ) (hq : 1 ≤ C.numF)
    (Pdec : Matrix (Idx n ℓ) (Idx n ℓ) ℂ) (hP : Pdec.IsHermitian) (hP2 : Pdec * Pdec = Pdec)
    (γ : Matrix (Qubits ℓ) (Qubits ℓ) ℂ) (htr : γ.trace.re ≤ 1)
    {C' : Type} [Fintype C'] [DecidableEq C'] (χ : EuclideanSpace ℂ (Qubits ℓ × C'))
    (hχ : ∀ c d, γ c d = ∑ e : C', χ (c, e) * star (χ (d, e))) :
    decisionAdvantage C Pdec γ ≤
      4 * ∑ i ∈ Finset.Icc 1 C.numF, expectFGX n (fun f g x =>
        ‖act (Matrix.kronecker (firstQueryProj (g x) * C.branchZ f g x i)
            (1 : Matrix C' C' ℂ))
          (WithLp.toLp 2 fun a : Idx n ℓ × C' =>
            if a.1.1 = (x, f (g x)) then χ (a.1.2, a.2) else 0)‖) ∧
    4 * ∑ i ∈ Finset.Icc 1 C.numF, expectFGX n (fun f g x =>
        ‖act (Matrix.kronecker (firstQueryProj (g x) * C.branchZ f g x i)
            (1 : Matrix C' C' ℂ))
          (WithLp.toLp 2 fun a : Idx n ℓ × C' =>
            if a.1.1 = (x, f (g x)) then χ (a.1.2, a.2) else 0)‖) ≤
      4 * Real.sqrt ((C.numF : ℝ) * ∑ i ∈ Finset.Icc 1 C.numF, C.bTerm γ i) := by sorry

end CatalystQLB.Query
