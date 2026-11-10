-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_4_3
-- name    : EzeunalaJiangKS.Signing.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:07:11.543903+00:00
-- url     : https://prove2.me/theorems/06394ad9-70eb-4f5b-b110-db2af31f74de
-- title:
--   Lemma 4.3 — First and second variations
-- statement:
--   At any normalized light state, for each active coordinate $i$ and each real direction $h$ on the active face,
--   $$\partial_i R=\alpha_i p_i-\beta_i q_i,$$
--   $$h^\top(\nabla^2R)h\le\tfrac{11}{4}E_h-c\sum_{i\text{ active}}\chi_i h_i^2(b_ip_i+a_iq_i),\qquad\chi_i=-\psi_i''-\tfrac43(\psi_i')^2/\psi_i>0.$$
--   The crossed weights $b_ip_i+a_iq_i$ and the fixed-$t$ energy are those defined from the actual optimizer and multipliers, with $c=40$. This states the complete first and second variation bounds, with all derivatives taken on the continuous open face. No linear independence of the input matrices is assumed.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - encoding: active coordinates relabeled by [n] → N-coordinate vectors and matrices zero on frozen indices, face-composed derivatives; reason: restriction to the active set is a linear identification with the same gradient, Hessian, trace, covariance and infinity norm
--   - encoding: v_i* Z v_i for any factor A_i=v_i v_i* → Re Tr(A_i Z) for the same rank-one matrix; reason: cyclicity of trace gives the same real scalar independently of the factor phase; no rational factor vectors are required
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 4.3, printed p. 13 (PDF p. 14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Energy

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 4.3, printed p.13 / PDF p.14. -/
theorem lemma_4_3 (N d : ℕ) (A : Fin N → CMat d) (x₀ x : State N)
    (hA : normalized A x₀) (hx : light A x₀ x) :
  (∀ i ∈ active x, facePartial (matrixPotential A x₀) x i =
      alpha A x₀ x i * scalarP A x₀ x i - beta A x₀ x i * scalarQ A x₀ x i) ∧
  (∀ h : State N, faceDirection x h →
    quadratic (faceHessian (matrixPotential A x₀) x) h ≤
      (11 / 4 : ℝ) * energy A x₀ x h - couplingConstant * ∑ i ∈ active x,
        chi (x i) * (h i)^2 *
          (scalarB A x₀ x i * scalarP A x₀ x i + scalarA A x₀ x i * scalarQ A x₀ x i)) ∧
  (∀ i ∈ active x, 0 < chi (x i)) := by sorry

end EzeunalaJiangKS.Signing
