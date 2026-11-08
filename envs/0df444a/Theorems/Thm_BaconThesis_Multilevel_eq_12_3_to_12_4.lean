-- Prove2me | Theorems.Thm_BaconThesis_Multilevel_eq_12_3_to_12_4
-- name    : BaconThesis.Multilevel.eq_12_3_to_12_4
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:37:21.296047+00:00
-- url     : https://prove2.me/theorems/d8d7eb2b-be77-402b-876f-154293617ec6
-- title:
--   Eqs. (12.3)–(12.4): both DF conditions force $\alpha_1=\alpha_2^*$ and $G|\psi\rangle=\alpha|\psi\rangle$ (corrected: necessity only)
-- statement:
--   Let $g_{ij}\in\mathbb C$ ($i>j$) be the coupling coefficients of an $N$-level atom, $\sigma_{ij}=|i\rangle\langle j|+|j\rangle\langle i|$, and $G$ the symmetric transition matrix of (12.4) ($G_{ij}=g_{ij}$ for $i>j$, $G_{ii}=0$, $G_{ij}=g_{ji}$ for $i<j$). Then:
--
--   1. the first generator of the OSR algebra is the operator with matrix $G$:
--   $$
--   \sum_{i>j=1}^{N} g_{ij}\sigma_{ij} = \sum_{i,j=1}^{N} G_{ij}|i\rangle\langle j| ;
--   $$
--   2. if a nonzero vector $|\psi\rangle$ satisfies both conditions (12.3),
--   $$
--   \sum_{i>j} g_{ij}\sigma_{ij}|\psi\rangle = \alpha_1|\psi\rangle, \qquad \sum_{i>j} g^{*}_{ij}\sigma_{ij}|\psi\rangle = \alpha_2|\psi\rangle,
--   $$
--   then $\alpha_1=\alpha_2^{*}$ and $\sum_{i,j} G_{ij}|i\rangle\langle j|\psi\rangle = \alpha_1|\psi\rangle$, which is (12.4).
--
--   So a DF state is in particular an eigenvector of the matrix $G$, whose spectrum therefore controls which states can satisfy the DF condition.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based); the coefficients $g_{ij}$ with $i\le j$ are ignored.
--
--   Differences from the source:
--   - correction: "the condition is really one condition" ((12.3) equivalent to (12.4) with α₁ = α₂*) → (12.3) implies α₁ = α₂* and (12.4); reason: the converse is false for complex g: N = 3, g₂₁ = 1, g₃₁ = i, g₃₂ = 0, ψ = (0, −i, 1) gives Gψ = 0 but Σ g*_ij σ_ij ψ = (−2i, 0, 0) ≠ 0 = α₁* ψ
--   - encoding: |ψ⟩ in a DF subspace defined by α₁ and α₂ → any nonzero vector ψ satisfying both equations (12.3); reason: the step uses only (12.3) at one state; the states of a DF subspace are exactly such vectors
--   - encoding: levels 1…N and coefficients g_ij for i > j → Fin N (0-based) and g : Fin N → Fin N → ℂ with the entries for i ≤ j ignored; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §12.1, eqs. (12.3)–(12.4), p.156 (PDF p.173)

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_sumSigma
import Definitions.Def_BaconThesis_Multilevel_Gmat

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§12.1, eqs. (12.3)–(12.4), p.156 (PDF p.173): `Σ_{i>j} g_ij σ_ij = Σ_{i,j} G_ij |i⟩⟨j|` with `G`
the symmetric matrix of (12.4), and if a nonzero `|ψ⟩` satisfies both conditions (12.3),
`Σ_{i>j} g_ij σ_ij|ψ⟩ = α₁|ψ⟩` and `Σ_{i>j} g*_ij σ_ij|ψ⟩ = α₂|ψ⟩`, then `α₁ = α₂*` and
`Σ_{i,j} G_ij |i⟩⟨j|ψ⟩ = α₁|ψ⟩` (12.4).

**Formalization Note.** Levels are `Fin N` (0-based); only `g i j` with `j < i` enter. The book's
remark that "the condition is really one condition" is stated in its true direction only: (12.3)
implies `α₁ = α₂*` and (12.4); the converse fails for complex `g` (`N = 3`, `g₂₁ = 1`, `g₃₁ = i`,
`g₃₂ = 0`: `ψ = (0, −i, 1)` has `Gψ = 0` but `G*ψ ≠ 0`). -/
theorem eq_12_3_to_12_4 {N : ℕ} (g : Fin N → Fin N → ℂ) :
    sumSigma g = Gmat g ∧
      ∀ (ψ : Fin N → ℂ) (α₁ α₂ : ℂ), ψ ≠ 0 →
        sumSigma g *ᵥ ψ = α₁ • ψ →
        sumSigma (fun i j => star (g i j)) *ᵥ ψ = α₂ • ψ →
        α₁ = star α₂ ∧ Gmat g *ᵥ ψ = α₁ • ψ := by sorry

end BaconThesis.Multilevel
