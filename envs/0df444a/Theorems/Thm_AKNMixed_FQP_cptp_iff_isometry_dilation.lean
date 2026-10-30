-- Prove2me | Theorems.Thm_AKNMixed_FQP_cptp_iff_isometry_dilation
-- name    : AKNMixed.FQP.cptp_iff_isometry_dilation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:14:54.910996+00:00
-- url     : https://prove2.me/theorems/fa4efde1-8d1a-4b7d-a684-ebb22655c1c3
-- title:
--   Lemma 1 — trace preserving and completely positive iff $T\rho=\mathrm{Tr}_F(V\rho V^\dagger)$ with $\dim F\le\dim N\dim M$ (corrected: $V:N\to M\otimes F$)
-- statement:
--   Let $\mathcal N$ and $\mathcal M$ be finite-dimensional Hilbert spaces and $T:\mathbf L(\mathcal N)\to\mathbf L(\mathcal M)$ a linear super-operator. The following are equivalent:
--
--   1. $T$ is trace preserving and completely positive;
--   2. there are a Hilbert space $\mathcal F$ with $\dim\mathcal F\le\dim\mathcal N\cdot\dim\mathcal M$ and an isometry ("unitary embedding") $V:\mathcal N\to\mathcal M\otimes\mathcal F$, $V^{\dagger}V=I$, such that
--
--   $$T\rho=\operatorname{Tr}_{\mathcal F}\bigl(V\rho V^{\dagger}\bigr)\qquad\text{for all }\rho\in\mathbf L(\mathcal N).$$
--
--   This is the Stinespring form of a quantum operation with a bound on the environment, and it is the step from general gates to unitary ones (Lemma 4).
--
--   Differences from the source:
--   - correction: V : N → N ⊗ F → V : N → M ⊗ F (Matrix (κ × Fin r) ι ℂ); reason: as printed the statement does not typecheck unless M = N: for T the partial trace from two qubits to one (trace preserving, completely positive) no V : N → N ⊗ F gives Tr_F(VρV†) ∈ L(M); Lemma 4's proof on p. 9 uses V : N → M ⊗ F
--   - encoding: a Hilbert space F; a unitary embedding V → F = ℂ^r with r ≤ |ι|·|κ|; V with Vᴴ V = 1; reason: every finite-dimensional Hilbert space is some ℂ^r; a unitary embedding is an isometry (p. 6: |ξ⟩ ↦ |ξ⟩ ⊗ |0⟩)
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 1, p. 6

import Mathlib
import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_WildeQIT_partialTrace

namespace AKNMixed.FQP

open Matrix

/-- **Lemma 1: a super-operator is trace preserving and completely positive iff it is
`ρ ↦ Tr_F(V ρ V†)` for an isometry `V : N → M ⊗ F` with `dim F ≤ dim N · dim M`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 1, p. 6: "The following conditions are equivalent: 1. A super-operator T : L(N) → L(M) is
trace-preserving and completely positive. 2. There is a Hilbert space F with
dim(F) ≤ dim(N) dim(M), and a unitary embedding V : N → N ⊗ F such that Tρ = Tr_F(VρV†)
∀ρ ∈ L(N)."

For finite index types `ι` (a basis of `N`) and `κ` (a basis of `M`) and a linear map
`T : L(N) → L(M)`: `T` preserves traces and is completely positive if and only if there are
`r ≤ |ι|·|κ|` and a matrix `V : N → M ⊗ ℂ^r` with `V† V = I` such that
`T ρ = Tr_{ℂ^r}(V ρ V†)` for every `ρ`.

**Formalization Note.** The codomain of `V` is `M ⊗ F` (`κ × Fin r`), not the printed `N ⊗ F`
(a correction: see the differences list). A "unitary embedding" is an isometry, `V†V = I`
(p. 6: `|ξ⟩ ↦ |ξ⟩ ⊗ |0⟩` is one). `F = ℂ^r`; every finite-dimensional Hilbert space is one.
`Tr_F` is `WildeQIT.partialTraceRight`, complete positivity is
`PeresTerno.IsCompletelyPositive`. -/
theorem cptp_iff_isometry_dilation {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (T : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) :
    ((∀ ρ : Matrix ι ι ℂ, (T ρ).trace = ρ.trace) ∧ PeresTerno.IsCompletelyPositive T) ↔
      ∃ r : ℕ, r ≤ Fintype.card ι * Fintype.card κ ∧
        ∃ V : Matrix (κ × Fin r) ι ℂ, Vᴴ * V = 1 ∧
          ∀ ρ : Matrix ι ι ℂ, T ρ = WildeQIT.partialTraceRight (V * ρ * Vᴴ) := by sorry

end AKNMixed.FQP
