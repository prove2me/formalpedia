-- Prove2me | Theorems.Thm_BootRobust_NWDual_fenchel_xlogx
-- name    : BootRobust.NWDual.fenchel_xlogx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:50.188961+00:00
-- url     : https://prove2.me/theorems/bda6377c-572a-46fd-9512-21db0ef1179a
-- title:
--   B.8, p. 32 — Fenchel step: sup over λ ≥ 0 of λb − νλ log λ equals ν exp(b/ν − 1)
-- statement:
--   Let $\nu>0$ and $b\in\mathbb R$. Then
--   $$\sup_{\lambda\ge0}\big(\lambda b-\nu\lambda\log\lambda\big)=\nu\exp\Big(\frac b\nu-1\Big),$$
--   with the convention $0\log0=0$, and the supremum is attained (at $\lambda=e^{b/\nu-1}$).
--
--   This is the Fenchel conjugate of $\lambda\mapsto\nu\lambda\log\lambda$ on $[0,\infty)$; it evaluates the inner maximization over each coordinate $P_i$ of the Lagrangian in the proof of Lemma 2.
--
--   **Formalization Note** The value at $\lambda=0$ uses Lean's `Real.log 0 = 0`, which is the convention $0\log 0=0$.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, B.8 (proof of Lemma 2), p. 32, 'The inner maximization problems over λ can be dealt with using the Fenchel conjugate of the λ ↦ λ · log λ function'

import Mathlib
import Definitions.Def_BootRobust_NWDual_Setting

namespace BootRobust.NWDual

/-- B.8, p. 32 (Fenchel step): for `ν > 0`, `sup_{λ ≥ 0} (λ b − ν λ log λ) = ν exp(b/ν − 1)`,
and the supremum is attained. At `λ = 0` the term `λ log λ` is `0` (Lean's `Real.log 0 = 0`). -/
theorem fenchel_xlogx (ν b : ℝ) (hν : 0 < ν) :
    IsGreatest {x : ℝ | ∃ lam : ℝ, 0 ≤ lam ∧ x = lam * b - ν * lam * Real.log lam}
      (ν * Real.exp (b / ν - 1)) := by sorry

end BootRobust.NWDual
