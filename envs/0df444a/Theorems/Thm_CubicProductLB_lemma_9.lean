-- Prove2me | Theorems.Thm_CubicProductLB_lemma_9
-- name    : CubicProductLB.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:17:49.101032+00:00
-- url     : https://prove2.me/theorems/093b703c-bd41-4875-9e3f-1dde7f4f4115
-- title:
--   Lemma 9 — disjoint invertible minor and affine-product form of a quadratic
-- statement:
--   Let $Q$ be a polynomial of degree at most two over $\mathbb F_3$ and let $C$ be its off-diagonal coefficient matrix. There are disjoint index sets $I, J$, each of size $r$, for which $D = C(I, J)$ is invertible, and affine forms $A_1, B_1, \dots, A_m, B_m$ with $m \le 3r + 1$ such that
--   $$Q(x) = \sum_{\ell=1}^m A_\ell(x) B_\ell(x) \quad \text{for every } x \in X_n.$$
--   The equality is of functions on $X_n$, not of formal polynomials. The statement ties the number of affine products to the size of a disjoint invertible minor.
--
--   **Formalization Note** The index sets are the images of injective maps $u, v$ with disjoint ranges, which also orders the rows and columns of $D$.
--
--   Differences from the source:
--   - reading: an implicit r in "There are disjoint index sets I, J, each of size r" → r existentially quantified along with I, J; reason: the proof chooses r itself (a maximal minor, the empty one allowed); the page gives no other r
--   - encoding: index sets I, J with minor C(I, J) → injective maps u, v : Fin r → Fin n with disjoint ranges and the submatrix of offDiag Q; reason: invertibility does not depend on the order of rows and columns
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 9, Eq. (49), p.10

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_AffineForm
import Definitions.Def_CubicProductLB_offDiag

namespace CubicProductLB

/-- Lemma 9 (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Lemma 9, Eq. (49), p.10). A polynomial `Q` of degree at most two has disjoint index
sets `I = u(Fin r)`, `J = v(Fin r)` with `C(I, J)` invertible, and agrees on `X_n` with a sum of at most
`3r + 1` products of two affine forms.

**Formalization Note** The page's `r` is implicit and is quantified existentially, as the proof
chooses it (a maximal such minor; the empty minor `r = 0` is allowed). -/
theorem lemma_9 {n : ℕ} (Q : MvPolynomial (Fin n) (ZMod 3)) (hQ : Q.totalDegree ≤ 2) :
    ∃ (r : ℕ) (u v : Fin r → Fin n),
      Function.Injective u ∧ Function.Injective v ∧ (∀ a b, u a ≠ v b) ∧
      IsUnit ((offDiag Q).submatrix u v).det ∧
      ∃ m ≤ 3 * r + 1, ∃ A B : Fin m → AffineForm n,
        ∀ x ∈ signCube n,
          MvPolynomial.eval x Q = ∑ l, AffineForm.eval (A l) x * AffineForm.eval (B l) x := by sorry

end CubicProductLB
