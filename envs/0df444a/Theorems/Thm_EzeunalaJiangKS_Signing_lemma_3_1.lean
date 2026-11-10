-- Prove2me | Theorems.Thm_EzeunalaJiangKS_Signing_lemma_3_1
-- name    : EzeunalaJiangKS.Signing.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:04:06.930072+00:00
-- url     : https://prove2.me/theorems/07b7fc13-fdf9-402b-9636-e9ef954aabdc
-- title:
--   Lemma 3.1 — Matrix potential
-- statement:
--   For every normalized input, rational start $x^0$, and $x\in[-1,1]^N$, the optimization defining $R(x)$ has exactly one minimizing triple. Its objective equals the independently defined infimum. The chosen minimizer and $R$ are $C^\infty$ on every open face with frozen coordinates fixed, including vertex faces. Moreover,
--   $$\|S(x)\|\le R(x)\le\|S(x)\|+2\sqrt{c\nu+2d\varepsilon}=\|S(x)\|+2\sqrt{(c+2)\nu},$$
--   and for every allowed $\lambda$,
--   $$\Psi(x^0)\le(2\sqrt{42}+1/100)\sqrt\nu\le13\sqrt\nu.$$
--   Here $c=40$, $\varepsilon=\nu/d$. The initial coefficient is $2\sqrt{42}+1/100$. Attainment, uniqueness, and smoothness are conclusions, not fields of the input. This identifies the potential as a smooth spectral bound without changing its inequality-constrained definition.
--
--   Differences from the source:
--   - generalization: the exact normalized variance is assumed rational in the normalization discussion → the exact variance is used without assuming rationality; reason: rationality is used for implementation, not the analytic identities or estimates; this includes every rational-variance source instance and leaves rational-proxy implementation to the goal proof
--   - generalization: the analytic lambda is sqrt(nu)/(100N), with rational replacements in the indicated interval → every real lambda in the full closed permitted interval; reason: the analytic estimates use positivity and the interval bounds, so this covers the exact choice and every permitted rational replacement
--   - encoding: active coordinates relabeled by [n] → N-coordinate vectors and matrices zero on frozen indices, face-composed derivatives; reason: restriction to the active set is a linear identification with the same gradient, Hessian, trace, covariance and infinity norm
--   - encoding: minimum in (5) with unique minimizer → independent real infimum, universal minimizing predicate, and explicit objective equals infimum clause; reason: the added equality connects the chosen optimizer to the infimum definition; feasible objectives are nonempty and bounded below on valid data
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), Lemma 3.1, printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_FaceCalculus

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

/-- Lemma 3.1, printed p.4 / PDF p.5. -/
theorem lemma_3_1 (N d : ℕ) (A : Fin N → CMat d) (x₀ : State N)
    (hA : normalized A x₀) :
  (∀ x : State N, cube x →
    (∃! z : Primal d, isOptimizer A x₀ x z) ∧
    objective A (optimizer A x₀ x) = matrixPotential A x₀ x ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => optimizer A x₀ (faceMap x y)) (faceDomain x) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => matrixPotential A x₀ (faceMap x y)) (faceDomain x) ∧
    spectral (shift A x₀ x) ≤ matrixPotential A x₀ x ∧
    matrixPotential A x₀ x ≤ spectral (shift A x₀ x) +
      2 * Real.sqrt (couplingConstant * variance A + 2 * d * epsilon A) ∧
    spectral (shift A x₀ x) + 2 * Real.sqrt (couplingConstant * variance A + 2 * d * epsilon A) =
      spectral (shift A x₀ x) + 2 * Real.sqrt ((couplingConstant + 2) * variance A)) ∧
  (∀ l : ℝ, allowedLambda A l →
    potential A x₀ l x₀ ≤ (2 * Real.sqrt 42 + 1 / 100) * Real.sqrt (variance A) ∧
    (2 * Real.sqrt 42 + 1 / 100) * Real.sqrt (variance A) ≤ 13 * Real.sqrt (variance A)) := by sorry

end EzeunalaJiangKS.Signing
