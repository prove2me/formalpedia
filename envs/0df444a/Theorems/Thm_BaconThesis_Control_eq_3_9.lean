-- Prove2me | Theorems.Thm_BaconThesis_Control_eq_3_9
-- name    : BaconThesis.Control.eq_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:58:49.461948+00:00
-- url     : https://prove2.me/theorems/f70bcb64-ef39-4a21-a1dd-09182d4cbd4e
-- title:
--   (3.8) ⇒ (3.9) — each term of the traced commutator condition vanishes separately
-- statement:
--   Let $(F_\alpha)$ be a fixed basis of the system operators with $F_0 = I/\sqrt d$, let $H$ be an operator on $\mathcal H_S\otimes\mathcal H_A$ with apparatus operators $A_\alpha$ and apparatus Hamiltonian $H_A$, and let $|a\rangle$ be an apparatus vector. Expand a system density matrix as in (3.7), $\rho_S = \frac1d I + \sum_{\alpha\neq0}\rho_\alpha F_\alpha$, $\rho_\alpha = \mathrm{Tr}[F_\alpha\rho_S]$. If for every system density matrix $\rho_S$
--   $$
--   \sum_{\alpha\neq0}\rho_\alpha\,\big[A_\alpha,|a\rangle\langle a|\big] + \big[H_A,|a\rangle\langle a|\big] = 0, \tag{3.8}
--   $$
--   then
--   $$
--   \big[A_\alpha,|a\rangle\langle a|\big] = 0\quad(\alpha\neq0),\qquad \big[H_A,|a\rangle\langle a|\big] = 0. \tag{3.9}
--   $$
--
--   The coefficient vectors $(\rho_\alpha)_{\alpha\neq0}$ of density matrices contain the origin and a ball around it, which is why the terms separate.
--
--   Differences from the source:
--   - encoding: real coefficients ρ_α of the expansion (3.7) → ρ_α = Tr[F_α ρ_S] in ℂ; reason: by trace orthonormality these are the coefficients of (3.7), real for Hermitian F_α; same instances
--   - encoding: A_α and H_A given by the expansion (3.3) → A_α = Tr_S[(F_α ⊗ I)H] and H_A = Tr_S[H]/d; reason: for a trace-orthonormal Hermitian basis these are the unique operators of (3.3); same instances
--   - generalization: H the Hermitian system-apparatus Hamiltonian and |a⟩ a pure state → any operator H and any vector |a⟩; reason: the deduction uses only that ρ_S ranges over all density matrices; the book's case is an instance
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eqs. (3.7)–(3.9), pp.32–33 (PDF pp.49–50)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Control_IsFixedBasis
import Definitions.Def_BaconThesis_Control_coeffOp
import Definitions.Def_BaconThesis_Control_HA

open scoped Matrix

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eqs. (3.7)–(3.9), pp.32–33 (PDF pp.49–50): "This in turn implies that each of the terms in
the expansion of Eq. (3.8) must vanish separately [Aα, |a⟩⟨a|] = 0 [HA, |a⟩⟨a|] = 0." For a fixed
basis `F` (index `i0` for `α = 0`), if for every system density matrix `ρ_S`, with coefficients
`ρ_α = Tr[F_α ρ_S]` of the expansion (3.7),
`Σ_{α≠0} ρ_α [A_α, |a⟩⟨a|] + [H_A, |a⟩⟨a|] = 0` (3.8), then `[A_α, |a⟩⟨a|] = 0` for every
`α ≠ 0` and `[H_A, |a⟩⟨a|] = 0` (3.9).

**Formalization Note.** `A_α = coeffOp H F α`, `H_A = HA H`; `ρ_α = Tr[F_α ρ_S]` are the expansion
coefficients of (3.7) (real for Hermitian `F_α`, taken in `ℂ`). `H` and `|a⟩` are arbitrary. -/
theorem eq_3_9 {s a κ : Type} [Fintype s] [DecidableEq s] [Fintype a] [DecidableEq a]
    [Fintype κ] [DecidableEq κ]
    (H : Matrix (s × a) (s × a) ℂ) (F : κ → Matrix s s ℂ) (i0 : κ) (hF : IsFixedBasis F i0)
    (v : a → ℂ)
    (h38 : ∀ ρ : Matrix s s ℂ, WildeQIT.IsDensityOperator ρ →
      ∑ α ∈ Finset.univ.erase i0, (F α * ρ).trace •
          (coeffOp H F α * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * coeffOp H F α) +
        (HA H * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * HA H) = 0) :
    (∀ α, α ≠ i0 →
      coeffOp H F α * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * coeffOp H F α = 0) ∧
    HA H * Matrix.vecMulVec v (star v) - Matrix.vecMulVec v (star v) * HA H = 0 := by sorry

end BaconThesis.Control
