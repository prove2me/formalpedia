-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_4_7
-- name    : EzeunalaJiangKS.Signing.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:08:49.006036+00:00
-- url     : https://prove2.me/theorems/204c174c-9fd5-48f2-b366-94de30a79c02
-- title:
--   Lemma 4.7 — Covariance
-- statement:
--   For each normalized input and rational start there is a $C_1$ independent of the light state, with $1\le C_1\le B(N+d+1)^k$ for absolute $B\ge1,k$ fixed before all data. At every light state with $n$ active coordinates there is a centered finitely supported random direction $h$ such that, writing $\omega_i=T_i^2\mathbb E[h_i^2]$,
--   $$\mathbb E[E_h]\le8\sum_{i\text{ active}}(\widetilde a_i\widetilde p_i+\widetilde b_i\widetilde q_i)\omega_i,\qquad\sum_{i\text{ active}}\omega_i\ge n/C_1,\qquad\omega_i\le C_1.$$
--   The last inequality holds on every active coordinate. The atom count is arbitrary and chosen with the distribution; all expectations are weighted finite sums. This controls the actual fixed-$t$ barrier energy while retaining nonzero total movement.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - encoding: active coordinates relabeled by [n] → N-coordinate vectors and matrices zero on frozen indices, face-composed derivatives; reason: restriction to the active set is a linear identification with the same gradient, Hessian, trace, covariance and infinity norm
--   - encoding: v_i* Z v_i for any factor A_i=v_i v_i* → Re Tr(A_i Z) for the same rank-one matrix; reason: cyclicity of trace gives the same real scalar independently of the factor phase; no rational factor vectors are required
--   - encoding: centered finitely supported random direction → a positive finite atom count, nonnegative weights totaling one, and weighted mean zero; reason: every such finite law has this representation and no support size is fixed in advance
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 4.7, printed p. 19 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_FiniteLaw

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 4.7, printed p.19 / PDF p.20. -/
theorem lemma_4_7 :
  ∃ (B : ℝ) (k : ℕ), 1 ≤ B ∧
  ∀ (N d : ℕ) (A : Fin N → CMat d) (x₀ : State N), normalized A x₀ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ C₁ ≤ B * ((N + d + 1 : ℕ) : ℝ)^k ∧
  ∀ x : State N, light A x₀ x →
  ∃ D : FiniteDirection N, D.valid x ∧
    D.expect (energy A x₀ x) ≤ 8 * ∑ i ∈ active x,
      (scaledA A x₀ x i * scaledP A x₀ x i + scaledB A x₀ x i * scaledQ A x₀ x i) *
        motionWeight A x₀ x D i ∧
    (activeCount x : ℝ) / C₁ ≤ ∑ i ∈ active x, motionWeight A x₀ x D i ∧
    ∀ i ∈ active x, motionWeight A x₀ x D i ≤ C₁ := by sorry

end EzeunalaJiangKS.Signing
