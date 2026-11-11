-- Prove2me | Theorems.Thm_AgnGaussTomo_lemma_3_11
-- name    : AgnGaussTomo.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:24:09.890198+00:00
-- url     : https://prove2.me/theorems/dfd22eec-6fd0-4d14-bd6a-040da0234c3b
-- title:
--   Lemma 3.11 — derivative bounds $\|D^k\psi(\theta)[h_1,\dots,h_k]\|_2\le C_D^kk!\prod\|h_i\|_{\mathcal P}$
-- statement:
--   There is a universal constant $C_D$ such that for every $n$, every $k\ge1$, every $\theta\in\mathcal P_n$ with $\|\theta\|_{\mathcal P}\le1/8$ and all directions $h_1,\dots,h_k\in\mathcal P_n$, the map $\theta\mapsto|\psi(\theta)\rangle$ is $k$ times continuously differentiable at $\theta$ and
--
--   $$
--   \big\|\,|D^k\psi(\theta)[h_1,\dots,h_k]\rangle\big\|_2\le C_D^k\,k!\,\prod_{i=1}^k\|h_i\|_{\mathcal P}.
--   $$
--
--   The bound is of analytic type, uniformly in the number of modes; it yields the Taylor control behind the Hessian estimate of Proposition 3.9.
--
--   Differences from the source:
--   - reading: C_D → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - reading: ‖D^kψ(θ)[h₁, …, h_k]‖₂ (derivatives presupposed to exist) → ψ is k times continuously differentiable at θ, and the bound holds for Mathlib's iteratedFDeriv; reason: the printed bound presupposes the derivatives; asserting them excludes a junk zero derivative
--   - encoding: ψ(θ) as a map P_n → Fock space → psi : Pspace n → ℓ²(ℕⁿ), with ‖·‖_P the Euclidean norm of Pspace n; reason: for ‖θ‖_P ≤ 1/8, ‖A‖_op ≤ √2/8 < 1, so psi is the Bargmann state on a neighbourhood of θ
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.11, printed p. 20 (PDF p. 23); proof in App. A.2.4

import Mathlib
import Definitions.Def_AgnGaussTomo_psi

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Lemma 3.11: derivatives of the Bargmann state.** Arulandu, Chen, Chen, Li, Ma, *Finding Gaussian
Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Lemma 3.11, printed p. 20
(PDF p. 23): "There is a universal constant C_D such that, for every k ≥ 1, ‖θ‖_P ≤ 1/8, and
directions h₁, …, h_k ∈ P, ‖|D^k ψ(θ)[h₁, …, h_k]⟩‖₂ ≤ C_D^k k! ∏_{i=1}^k ‖h_i‖_P."

**Formalization Note.** `ψ(θ)` is `psi θ`, viewed as a map from the real Hilbert space `Pspace n`
to the Fock space `ℓ²(ℕⁿ)`; `D^k ψ(θ)` is Mathlib's `iteratedFDeriv ℝ k`. For `‖θ‖_P ≤ 1/8` one has
`‖A‖_op ≤ √2/8 < 1`, so `psi` is the Bargmann state on a neighbourhood. The statement also asserts
that `psi` is `k` times continuously differentiable at `θ`, which the printed bound presupposes; this
rules out a junk zero derivative. `C_D` is universal (before `n` and `k`). -/
theorem lemma_3_11 : ∃ C_D : ℝ, ∀ (n k : ℕ), 1 ≤ k → ∀ θ : Pspace n, ‖θ‖ ≤ 1 / 8 →
    ContDiffAt ℝ k (psi (n := n)) θ ∧
    ∀ h : Fin k → Pspace n,
      ‖iteratedFDeriv ℝ k (psi (n := n)) θ h‖ ≤ C_D ^ k * (k.factorial : ℝ) * ∏ i, ‖h i‖ := by sorry

end AgnGaussTomo
