-- Prove2me | Theorems.Thm_EFI1PRS_Uniform_conditional_clifford_extraction
-- name    : EFI1PRS.Uniform.conditional_clifford_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T05:03:29.155201+00:00
-- url     : https://prove2.me/theorems/ad735a42-d02e-40da-92be-a394725106c9
-- title:
--   Fact 2.16 — conditional Clifford extraction
-- statement:
--   Let $A=A_1A_2$ have $m$ qubits, with $\ell\le m$ qubits in $A_1$, let $B$ be any nonzero finite-dimensional register, and let $\zeta_{AB}$ be normalized. For $\varepsilon>0$ and real $k$, assume
--
--   $$H_{\min}^{\varepsilon/12}(A\mid B)_\zeta\ge k,\qquad\ell\le\frac{m+k}{2}-\log_2(1/\varepsilon).$$
--
--   Uniformly averaging over the complete Clifford group modulo global phase gives
--
--   $$\mathbb E_U D\bigl(\operatorname{Tr}_{A_2}(U\zeta U^\dagger),\mathsf{MM}_{A_1}\otimes\zeta_B\bigr)\le\varepsilon.$$
--
--   The same trace-distance bound holds with the Clifford seed included as a public classical register. The unitary acts on $A$ alone, and $k$ is not assumed nonnegative.
--
--   Differences from the source:
--   - encoding: a supremum of domination exponents, with purified-distance smoothing → EReal suprema, trace-one reference states and the full published subnormalized purified-distance ball; reason: infinite entropy is represented without a junk real supremum or a support restriction
--   - encoding: uniform sampling from the finite Clifford group modulo scalar phase → an arbitrary finite enumeration of the published physical-conjugation quotient; reason: the probability is enumeration independent; existence and the cardinality of such an enumeration are obligations of Lemma 2.17
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Fact 2.16, PDF/printed p. 10

import Definitions.Def_EFI1PRS_Uniform_Generator

/-! Rishabh Batra, EFI ⇔ 1PRS, pinned October 2026 STOC submission #273.
Statement-preparation draft; proof is a future solver obligation. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conditional_clifford_extraction (m ell : ℕ) (hell : ell ≤ m)
    [Fintype (QAlgorithms.Clifford.ProjectiveGroup m)]
    {B : Type*} [Fintype B] [Nonempty B]
    (ζ : Matrix (Qubits m × B) (Qubits m × B) ℂ) (hζ : IsDensityMatrix ζ)
    (ε k : ℝ) (hε0 : 0 < ε)
    (hmin : (k : EReal) ≤ smoothConditionalMin ζ (ε/12))
    (hwidth : (ell : ℝ) ≤ ((m : ℝ)+k)/2-Real.logb 2 (1/ε)) :
    (∑ U : QAlgorithms.Clifford.ProjectiveGroup m,
      distance (extractColumn m ell (cliffordMatrix U) ζ) (idealExtracted m ell ζ)) /
        (Fintype.card (QAlgorithms.Clifford.ProjectiveGroup m) : ℝ) ≤ ε ∧
    distance (classicalUniform (fun U : QAlgorithms.Clifford.ProjectiveGroup m =>
      extractColumn m ell (cliffordMatrix U) ζ))
      (classicalUniform (fun _ : QAlgorithms.Clifford.ProjectiveGroup m => idealExtracted m ell ζ)) ≤ ε := by sorry

end EFI1PRS.Uniform
