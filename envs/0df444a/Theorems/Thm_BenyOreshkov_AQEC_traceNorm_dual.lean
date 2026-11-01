-- Prove2me | Theorems.Thm_BenyOreshkov_AQEC_traceNorm_dual
-- name    : BenyOreshkov.AQEC.traceNorm_dual
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:20:40.45632+00:00
-- url     : https://prove2.me/theorems/c2a87828-ec7e-4a67-b2c4-19f6cdacf6da
-- title:
--   Proof of Theorem 1, p. 2 — $\max_U|\mathrm{Tr}(XU)|=\mathrm{Tr}|X|$, and $|\mathrm{Tr}(XA')|\le\mathrm{Tr}|X|$ on the unit ball
-- statement:
--   Let $X$ be a square complex matrix and $|X|=\sqrt{X^\dagger X}$. Then
--   $$
--   \max_{U\ \text{unitary}}\big|\mathrm{Tr}(XU)\big| = \mathrm{Tr}|X|,
--   $$
--   the maximum being attained, and $|\mathrm{Tr}(XA')|\le\mathrm{Tr}|X|$ for every operator $A'$ with $\|A'\|\le1$. In the proof of Theorem 1 this is applied to the operator $X_\rho$ with $|g_\rho(A,U')|=|\mathrm{Tr}(X_\rho U')|$: the inner maximum is the trace norm of $X_\rho$, and it does not change when $U'$ ranges over the unit ball.
--
--   **Formalization Note** $\mathrm{Tr}|X|$ is the platform's trace norm `WildeQIT.traceNorm`; $\|A'\|\le1$ is $A'^\dagger A'\le1$ in the Loewner order.
--
--   Differences from the source: none.
-- source:
--   Bény, Oreshkov, General conditions for approximate quantum error correction and near-optimal recovery channels, arXiv:0907.5391v4, §Main result, proof of Theorem 1, p. 2

import Definitions.Def_WildeQIT_traceNorm

open Matrix WildeQIT
open scoped MatrixOrder

namespace BenyOreshkov.AQEC

/-- **Trace-norm duality.** Bény, Oreshkov, arXiv:0907.5391v4, proof of Theorem 1, p. 2: "we
know that max_U′ |Tr(X_ρU′)| = Tr(|X_ρ|)", and "the max over U′ can also be taken over operators
A′ in the unit ball since then |Tr(X_ρA′)| ≤ Tr(|X_ρ|)". For every square matrix `X`, the trace
norm `Tr|X|` is the largest value of `|Tr(XU)|` over unitaries `U` (attained), and
`|Tr(XA′)| ≤ Tr|X|` for every contraction `A′`.

**Formalization Note** `Tr|X|` is `WildeQIT.traceNorm X = Re Tr √(X†X)`; contractions are
`A′ᴴ * A′ ≤ 1` (operator norm at most 1). -/
theorem traceNorm_dual {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    IsGreatest {t : ℝ | ∃ U ∈ Matrix.unitaryGroup n ℂ, t = ‖(X * U).trace‖} (traceNorm X) ∧
      ∀ A' : Matrix n n ℂ, A'ᴴ * A' ≤ 1 → ‖(X * A').trace‖ ≤ traceNorm X := by sorry

end BenyOreshkov.AQEC
