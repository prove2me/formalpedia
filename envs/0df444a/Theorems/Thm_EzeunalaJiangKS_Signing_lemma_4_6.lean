-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_4_6
-- name    : EzeunalaJiangKS.Signing.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:06:13.260206+00:00
-- url     : https://prove2.me/theorems/4b9b7b3b-19d2-45eb-bfe4-8586cd1edbb8
-- title:
--   Lemma 4.6 — Scalar bounds
-- statement:
--   Under the normalized setting and the complementary light-state inequalities (13), there are absolute positive constants $C_s,c_*,C_t$, chosen before dimensions, data, state and coordinate, such that for every active $i$,
--   $$\widetilde a_i+\widetilde b_i\le C_s/c,\quad\widetilde a_i\widetilde b_i<1/c^2,$$
--   $$\frac{-\psi_i''}{T_i^2}\ge c_*,\quad\frac1{T_i^2}\le C_t,\quad\frac{|\psi_i'|}{\psi_i}\le\tfrac12(-\psi_i''),\quad\frac{\chi_i}{\alpha_i\beta_i}\ge\tfrac59.$$
--   Here $c=40$ and every scalar is the computed contraction or rescaling in the definition layer. These uniform inequalities state all three numbered clauses, interpreting the source's $O$ and $\Omega$ with absolute constants. They control the coordinate scales in the covariance and variation statements.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - encoding: active coordinates relabeled by [n] → N-coordinate vectors and matrices zero on frozen indices, face-composed derivatives; reason: restriction to the active set is a linear identification with the same gradient, Hessian, trace, covariance and infinity norm
--   - encoding: v_i* Z v_i for any factor A_i=v_i v_i* → Re Tr(A_i Z) for the same rank-one matrix; reason: cyclicity of trace gives the same real scalar independently of the factor phase; no rational factor vectors are required
--   - encoding: O(1/c), Omega(1), O(1) with absolute constants → three existential positive constants before all data and coordinates; reason: this is the uniform quantitative meaning of the printed asymptotic notation, with the paper constant c=40 fixed
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 4.6, printed p. 16 (PDF p. 17); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_ScalarData

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 4.6, printed p.16 / PDF p.17; implicit constants quantified absolutely. -/
theorem lemma_4_6 :
  ∃ Csum Clower Cinv : ℝ, 0 < Csum ∧ 0 < Clower ∧ 0 < Cinv ∧
  ∀ (N d : ℕ) (A : Fin N → CMat d) (x₀ : State N), normalized A x₀ →
  ∀ x : State N, light A x₀ x → ∀ i ∈ active x,
    (scaledA A x₀ x i + scaledB A x₀ x i ≤ Csum / couplingConstant ∧
      scaledA A x₀ x i * scaledB A x₀ x i < 1 / couplingConstant^2) ∧
    (Clower ≤ -psiSecond (x i) / (coordinateScale A x₀ x i)^2 ∧
      1 / (coordinateScale A x₀ x i)^2 ≤ Cinv ∧
      |psiPrime (x i)| / psi (x i) ≤ (1 / 2 : ℝ) * (-psiSecond (x i))) ∧
    chi (x i) / (alpha A x₀ x i * beta A x₀ x i) ≥ (5 / 9 : ℝ) := by sorry

end EzeunalaJiangKS.Signing
