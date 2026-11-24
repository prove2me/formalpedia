-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_5_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:55:30.497277+00:00
-- url     : https://prove2.me/theorems/a9d9d3de-794f-48c4-97ae-0b7471553aeb
-- title:
--   Theorem 5:2 — cg is the cd-method with A-orthogonalized residuals; orthogonal residuals force cg
-- statement:
--   Let $A$ be real symmetric positive definite.
--
--   1. The cg-method (5:1) is a cd-method: its estimates, residuals and directions satisfy (4:1)–(4:2).
--   2. Its directions are obtained by A-orthogonalization of the residuals:
--   $$p_i=r_i-\sum_{j<i}\frac{(r_i,Ap_j)}{(p_j,Ap_j)}\,p_j .$$
--   3. Conversely, a cd-method whose residuals $r_0,r_1,\dots$ are mutually orthogonal is essentially a cg-method: if the run does not terminate before step $n$ ($r_i\ne0$ for $i<n$), then there are nonzero scalars $s_i$ with $p_i=s_i\,p_i^{cg}$ for $i<n$, and $x_i=x_i^{cg}$, $r_i=r_i^{cg}$ for $i\le n$, where the superscript denotes the cg-method started at the same $x_0$.
--
--   The theorem places the cg-method inside the family of cd-methods and characterizes it there by the orthogonality of its residuals. The first sentence is also the published item `ConjGrad.Termination.cg_isCDRun` (stated there for the iteration of mission I); it is repeated here for the iteration of this mission so that the theorem is complete.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - reading: “essentially a cg-method” → runs with $r_i\ne0$ for $i<n$, directions equal to the cg directions up to nonzero factors, and equal estimates and residuals; reason: this is the meaning the paper gives in the paragraph after the theorem (p. 415): iterations terminating in fewer than $n$ steps are disregarded, and the directions are normalized
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 415, Theorem 5:2 and the paragraph defining “essentially” (PDF p. 7)

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:2 (Hestenes–Stiefel 1952, p. 415), with "essentially" as defined in the paragraph
after it: runs terminating in fewer than `n` steps are disregarded, and the directions are
identified up to nonzero scalar factors. -/
theorem theorem_5_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k : Fin n → ℝ) :
    (∀ x₀ : Fin n → ℝ, Termination.IsCDRun A k (fun i => (cgIter A k x₀ i).x)
      (fun i => (cgIter A k x₀ i).r) (fun i => (cgIter A k x₀ i).p)) ∧
    (∀ (x₀ : Fin n → ℝ) (i : ℕ), (cgIter A k x₀ i).p = (cgIter A k x₀ i).r -
      ∑ j ∈ Finset.range i,
        (((cgIter A k x₀ i).r ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).p)) /
          ((cgIter A k x₀ j).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ j).p))) • (cgIter A k x₀ j).p) ∧
    (∀ x r p : ℕ → Fin n → ℝ, Termination.IsCDRun A k x r p →
      (∀ i j, i ≠ j → r i ⬝ᵥ r j = 0) → (∀ i < n, r i ≠ 0) →
      ∃ s : ℕ → ℝ, (∀ i < n, s i ≠ 0 ∧ p i = s i • (cgIter A k (x 0) i).p) ∧
        ∀ i ≤ n, x i = (cgIter A k (x 0) i).x ∧ r i = (cgIter A k (x 0) i).r) := by sorry

end ConjGrad.ErrorDecrease.Supplement
