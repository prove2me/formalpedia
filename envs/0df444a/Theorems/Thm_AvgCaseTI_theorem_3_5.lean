-- Prove2me | Theorems.Thm_AvgCaseTI_theorem_3_5
-- name    : AvgCaseTI.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:43:30.887258+00:00
-- url     : https://prove2.me/theorems/84571cb0-6a73-42e2-b2d2-eee16522913b
-- title:
--   Theorem 3.5 — the spectral condition holds with probability $\ge\frac12e^{-23/9}$ and the eigenline is uniform
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is $N_0(q)\ge3$ such that for every $n\ge N_0(q)$, for a uniform matrix $H\in\mathrm M(n,q)$ conditioned on $\mathrm{Tr}(H^2)=0$:
--   1. with probability at least $\tfrac12e^{-23/9}$, $H$ has exactly one eigenvalue $\lambda$ in $\mathbb F_q$, which is nonzero and has algebraic multiplicity 1;
--   2. conditional on this event, the one-dimensional left eigenspace $\{v\in\mathbb F_q^{1\times n}:vH=\lambda v\}$ is uniformly distributed among the one-dimensional subspaces of $\mathbb F_q^{1\times n}$.
--
--   This transfers Theorem 6.11 to the algorithm: the normalized hull generator and its left eigenvector exist with constant probability, and the eigenvector carries no bias.
--
--   **Formalization Note** Clause 1 compares counts: $\tfrac12e^{-23/9}$ times the number of self-dual matrices is at most the number of self-dual matrices with the spectral property. Clause 2 says any two lines are the left eigenspace of equally many such matrices.
--
--   Differences from the source:
--
--   - encoding: "uniformly distributed among the one-dimensional subspaces" → any two lines are the eigenspace of equally many matrices of the event; reason: uniform distribution on a finite set is equality of counts
--   - reading: "for each fixed prime power q, there exists N₀(q)" → for each finite field K there is N₀; reason: all fields of order q are isomorphic and the counts are invariant; N₀ may be taken the same
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 3.5, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI

/-- **Theorem 3.5 (a self-dual matrix has a unique, nonzero, simple eigenvalue with constant
probability; its left eigenline is uniform).**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 3.5, p.18
(PDF p.20). For each finite field `F_q` there is `N₀(q) ≥ 3` such that for every `n ≥ N₀(q)`:
1. among the matrices `H ∈ M(n, q)` with `Tr(H²) = 0`, at least a fraction `½e^{−23/9}` have exactly
   one eigenvalue in `F_q`, which is nonzero and of algebraic multiplicity 1;
2. conditional on this event, the left eigenspace `{v ∈ F_q^{1×n} : vH = λv}` of the eigenvalue `λ`
   is uniformly distributed among the one-dimensional subspaces of `F_q^{1×n}`: any two lines are the
   eigenspace of equally many such `H`.

**Formalization Note.** Uniformity is equality of counts; `N₀` is chosen for the field `K` (equivalently
for `q`, all fields of order `q` being isomorphic). Row vectors are `Fin n → K` with `vecMul`. -/
theorem theorem_3_5 {K : Type*} [Field K] [Fintype K] :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      1 / 2 * Real.exp (-(23 / 9)) * (Nat.card {H : Mat K n // SelfDual H} : ℝ) ≤
        (Nat.card {H : Mat K n // SelfDual H ∧ UniqueSimpleNonzeroEig H} : ℝ) ∧
      ∀ ℓ ℓ' : Submodule K (Fin n → K),
        Module.finrank K ℓ = 1 → Module.finrank K ℓ' = 1 →
        Nat.card {H : Mat K n // SelfDual H ∧ UniqueSimpleNonzeroEig H ∧
            ∃ a : K, H.charpoly.IsRoot a ∧ leftEigenspace H a = ℓ} =
          Nat.card {H : Mat K n // SelfDual H ∧ UniqueSimpleNonzeroEig H ∧
            ∃ a : K, H.charpoly.IsRoot a ∧ leftEigenspace H a = ℓ'} := by sorry

end AvgCaseTI
