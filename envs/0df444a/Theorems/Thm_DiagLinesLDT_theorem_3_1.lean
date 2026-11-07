-- Prove2me | Theorems.Thm_DiagLinesLDT_theorem_3_1
-- name    : DiagLinesLDT.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:56:36.788442+00:00
-- url     : https://prove2.me/theorems/09ac37e1-a19f-4fff-9440-397ed7f5f607
-- title:
--   Theorem 3.1 — failure without the diagonal-lines test
-- statement:
--   For every prime power $q$, there is a two-prover projective strategy for the reduced low-individual-degree test with parameters $(m,d)=(2,2)$ that is accepted with probability 1. Writing $|\psi\rangle$ for its shared state and $A^u$ for Alice's point measurement, every projective measurement $G=\{G_g\}_g$ on Bob's Hilbert space whose outcomes are functions $g:\mathbb F_q^2\to\mathbb F_q$ satisfies
--
--   $$\mathbb E_{u\sim\mathbb F_q^2}\sum_{a\in\mathbb F_q}\sum_{g:\,g(u)=a}\langle\psi|A^u_a\otimes G_g|\psi\rangle\le 1-\frac1{16}\Big(1-\frac1q\Big)^3.$$
--
--   In particular, the right-hand side is at most $1-1/54$ for every $q\ge 3$, and equals $1-1/128$ for $q=2$.
--
--   So the axis-parallel and self-consistency tests alone do not have the quantum soundness property of the full low-individual-degree test: a perfect strategy can stay a constant distance from every global measurement.
--
--   **Formalization Note** The strategy is existentially quantified before $G$, and $G$ lives on that strategy's Bob space. The line player's question is the set $\ell$, and its answers must have degree at most 2.
--
--   Differences from the source:
--   - encoding: every prime power q → every finite field F, q = Fintype.card F; reason: finite fields of a given prime-power size exist and are isomorphic
--   - encoding: finite-dimensional Hilbert spaces and operators → ℂ^ι with matrices; reason: every finite-dimensional Hilbert space is one of these
--   - encoding: G with outcomes functions g → G indexed by all functions (Fin 2 → F) → F, zero operators allowed; reason: a measurement with outcomes in a subset of the functions extends by zero
--   - encoding: univariate polynomials f : ℓ → 𝔽_q of degree at most d → functions on ℓ agreeing with a polynomial of natDegree ≤ d along a parametrization; reason: the source writes the answers as functions on ℓ; legality is independent of the parametrization
--   - encoding: projective measurement → MIPRE.IsPVM: Hermitian idempotents summing to 1; reason: mutual orthogonality follows; zero outcomes are allowed as in the source
--   - encoding: ⟨ψ|M ⊗ N|ψ⟩ → its real part; reason: for tensors of Hermitian operators the value is already real
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), Theorem 3.1, p.5

import Mathlib
import Definitions.Def_DiagLinesLDT_reducedAcc

universe u

namespace DiagLinesLDT

/-- **Failure without the diagonal-lines test.** For every finite field `𝔽_q` there is a projective
strategy for the reduced test with `(m, d) = (2, 2)`, accepted with probability 1, whose consistency with
every projective measurement `G` on Bob's space with function outcomes is at most
`1 - (1/16)(1 - 1/q)³`. The bound is at most `1 - 1/54` for `q ≥ 3`, and equals `1 - 1/128` for `q = 2`.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), Theorem 3.1, p.5.

**Formalization Note** "Every prime power `q`" is every finite field `F` with `q = |F|`. The strategy comes
first and `G` lives on its Bob space, so the strategy cannot depend on `G`. Hilbert spaces are `ℂ^ι`. The
expectations are real parts (see `expect`), and `G` is indexed by all functions (see `consistency`). -/
theorem theorem_3_1 (F : Type u) [Field F] [Fintype F] [DecidableEq F] :
    (∃ (ιA ιB : Type u) (_ : Fintype ιA) (_ : DecidableEq ιA) (_ : Fintype ιB)
        (_ : DecidableEq ιB) (S : Strategy F 2 2 ιA ιB),
        S.IsProjective ∧ reducedAcc S = 1 ∧
          ∀ G : ((Fin 2 → F) → F) → Matrix ιB ιB ℂ, MIPRE.IsPVM G →
            consistency S G ≤ 1 - (1 / 16) * (1 - 1 / (Fintype.card F : ℝ)) ^ 3) ∧
      (3 ≤ Fintype.card F →
        1 - (1 / 16) * (1 - 1 / (Fintype.card F : ℝ)) ^ 3 ≤ 1 - 1 / 54) ∧
      (Fintype.card F = 2 →
        1 - (1 / 16) * (1 - 1 / (Fintype.card F : ℝ)) ^ 3 = 1 - 1 / 128) := by sorry

end DiagLinesLDT
