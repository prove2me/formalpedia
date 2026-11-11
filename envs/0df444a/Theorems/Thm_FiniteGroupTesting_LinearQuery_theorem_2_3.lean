-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_theorem_2_3
-- name    : FiniteGroupTesting.LinearQuery.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:34.757197+00:00
-- url     : https://prove2.me/theorems/d187a091-7ecb-4d94-bcfe-6d9e5febc1c4
-- title:
--   Theorem 2.3 — random Cayley expansion
-- statement:
--   Fix $0<\lambda<1$. There is $c_{\rm AR}(\lambda)>0$, independent of every finite group $H$ and its order $n$, such that $k=\lceil c_{\rm AR}\log n\rceil$ independent uniform samples, with their inverses and multiplicities, give a right Cayley transition operator $P$ satisfying
--
--   $$\Pr\left[\left\|P-\frac Jn\right\|_{2\to2}\le\lambda\right]\ge\frac{99}{100}.$$
--
--   The norm is on all real functions on $H$ and controls absolute nontrivial eigenvalues. For $n=1$ the zero-sample identity kernel equals $J/n$. Later invocations fix $\lambda_0=1/3000$ before choosing the sample constant. This is the submission's Alon–Roichman/Landau–Russell target; its appendix defines the norm but does not supply the promised proof.
--
--   Differences from the source:
--   - encoding: 2-to-2 norm bound on P-J/n → Euclidean norm inequality for every real vector; reason: this is the equivalent operator-norm inequality and avoids a real supremum default
--   - encoding: k=0 for the singleton, leaving the empty-multiset transition undefined → the empty-sample walk is the identity kernel; reason: on the singleton this equals J/n, so the same spectral conclusion holds without excluding a group order
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 14, Theorem 2.3; spectral conventions pp. 44–45

import Definitions.Def_FiniteGroupTesting_LinearQuery_RandomCayley

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

/-- Theorem 2.3, p. 14, with the full real 2-to-2 norm and symmetric multiplicities. -/
theorem theorem_2_3 (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam < 1) :
    ∃ cAR : ℝ, 0 < cAR ∧ ∀ (H : Type) [Group H] [Fintype H],
      (99/100 : ℝ) ≤ uniformProbability
        (fun a : Fin ⌈cAR * Real.log (Fintype.card H)⌉₊ → H => CayleyExpansion a lam) := by sorry

end FiniteGroupTesting.LinearQuery
