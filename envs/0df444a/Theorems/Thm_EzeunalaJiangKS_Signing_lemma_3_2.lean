-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_3_2
-- name    : EzeunalaJiangKS.Signing.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:03:46.255937+00:00
-- url     : https://prove2.me/theorems/69818bf5-098e-4571-b4f0-3f87674074a2
-- title:
--   Lemma 3.2 — Decreasing the potential
-- statement:
--   For every normalized input and rational starting point $x^0$, with allowed $\lambda$, one can choose $C_0>0$ independently of the nonterminal state. There are absolute $B\ge1$ and $k\in\mathbb N$, before the data, such that $C_0\le B(N+d+1)^k$. At every state $x$ with $n\ge1$ active coordinates, either some active coordinate can be set to $e\in\{-1,1\}$ with
--   $$\Psi(x^{i\gets e})\le\Psi(x)-\lambda\psi_i(x),$$
--   or there are a real drift $\mu$ and a positive semidefinite covariance $\Sigma$, on those active coordinates, such that
--   $$\|\mu\|_\infty\le C_0,\quad\operatorname{Tr}\Sigma\le C_0n,\quad\nabla\Psi\cdot\mu+\tfrac12\operatorname{Tr}((\nabla^2\Psi)\Sigma)\le-\lambda n/C_0.$$
--   These are analytic witnesses at every state, including heavy states through the endpoint alternative. No light-state condition is assumed globally. This lemma supplies a local progress certificate; it is not itself an executed randomized algorithm.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - generalization: the analytic lambda is sqrt(nu)/(100N), with rational replacements in the indicated interval → every real lambda in the full closed permitted interval; reason: the analytic estimates use positivity and the interval bounds, so this covers the exact choice and every permitted rational replacement
--   - encoding: active coordinates relabeled by [n] → N-coordinate vectors and matrices zero on frozen indices, face-composed derivatives; reason: restriction to the active set is a linear identification with the same gradient, Hessian, trace, covariance and infinity norm
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 3.2, printed p. 11 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf; identical restatement, first occurrence printed pp.4–5 (PDF pp.5–6)

import Definitions.Def_EzeunalaJiangKS_Signing_FaceCalculus

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 3.2, identical restatement printed p.11 / PDF p.12. -/
theorem lemma_3_2 :
  ∃ (B : ℝ) (k : ℕ), 1 ≤ B ∧
  ∀ (N d : ℕ) (A : Fin N → CMat d) (x₀ : State N), normalized A x₀ →
  ∀ l : ℝ, allowedLambda A l →
  ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ ≤ B * ((N + d + 1 : ℕ) : ℝ)^k ∧
  ∀ x : State N, cube x → 0 < activeCount x →
    (∃ i ∈ active x, ∃ e : ℝ, (e = -1 ∨ e = 1) ∧
      potential A x₀ l (Function.update x i e) ≤ potential A x₀ l x - l * psi (x i)) ∨
    (∃ (mu : State N) (U : RMat N), faceDirection x mu ∧ faceCovariance x U ∧
      U.PosSemidef ∧ (∀ i, |mu i| ≤ C₀) ∧ U.trace ≤ C₀ * activeCount x ∧
      generator (potential A x₀ l) x mu U ≤ -l * activeCount x / C₀) := by sorry

end EzeunalaJiangKS.Signing
