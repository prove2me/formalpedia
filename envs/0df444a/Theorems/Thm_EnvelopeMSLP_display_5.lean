-- Prove2me | Theorems.Thm_EnvelopeMSLP_display_5
-- name    : EnvelopeMSLP.display_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:10.652002+00:00
-- url     : https://prove2.me/theorems/5d56618f-21e0-4825-9233-2805e7c723f3
-- title:
--   Display (5), proof of Lemma 1 (corrected: re-arrangement needs m ≥ 2) — optimal-basis conditions are polynomial sign conditions
-- statement:
--   Let $D$ be an $m\times n$ matrix, $b\in\mathbb R^m$, $c\in\mathbb R^n$, $\beta$ an ordered basis, and write
--   $$P_i=\operatorname{adj}(D_\beta)_{(i,:)}b,\qquad Q=c_\beta\operatorname{adj}(D_\beta)D-c\det(D_\beta),$$
--   polynomials in the entries of the data.
--
--   1. If $\det D_\beta>0$, then $\beta$ is an optimal basis of (4) if and only if all $P_i\ge0$ and $Q\ge0$. This is display (5).
--   2. If $\det D_\beta\ne0$, then $\beta$ is optimal if and only if $\det(D_\beta)P_i\ge0$ for all $i$ and $\det(D_\beta)Q\ge0$.
--   3. The polynomial `detPoly β` evaluates to $\det D_\beta$.
--   4. If $m\ge2$ and $\det D_\beta\ne0$, the columns can be re-arranged so that the determinant becomes positive, and this does not change whether $\beta$ is optimal.
--   5. If $\beta$ is an optimal basis, its basic solution is optimal for (4).
--
--   Each condition is thus the sign of an explicit polynomial in the data, which is what makes $R_\beta$ semi-algebraic.
--
--   Differences from the source:
--   - correction: if det(Dβ) ≠ 0, we can always re-arrange columns of Dβ so that det(Dβ) > 0 → the re-arrangement clause assumes m ≥ 2; reason: for m = 1, D = (−1, 1), b = −1, c = 0, β = {1} is an optimal basis with det = −1 and no other arrangement
--   - generalization: display (5), for det(Dβ) > 0 only → also the sign-robust form for every det(Dβ) ≠ 0; reason: it covers m ≤ 1 and contains (5) at det(Dβ) > 0
--   - reading: β ⊆ [n] with |β| = m → an injection Fin m ↪ Fin n; reason: the sign of det(Dβ) depends on the column order, and the conditions of p.9 do not
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), proof of Lemma 1, display (5), p.9

import Mathlib
import Definitions.Def_EnvelopeMSLP_IsOptimalBasis
import Definitions.Def_EnvelopeMSLP_basicSolution
import Definitions.Def_EnvelopeMSLP_StdOptimal
import Definitions.Def_EnvelopeMSLP_lpData
import Definitions.Def_EnvelopeMSLP_detPoly
import Definitions.Def_EnvelopeMSLP_basicPoly
import Definitions.Def_EnvelopeMSLP_reducedPoly

namespace EnvelopeMSLP

/-- **Display (5): the optimal-basis conditions are polynomial sign conditions.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), proof of Lemma 1,
display (5), p.9. For an ordered basis `β` and data `(D, b, c)` of form (4), write `P_i` for `adj(D_β)_(i,:) b`
and `Q_j` for the `j`-th entry of `c_β adj(D_β) D − c det(D_β)`, polynomials in the data.
1. If `det D_β > 0`, then `β` is optimal iff all `P_i ≥ 0` and all `Q_j ≥ 0`. This is display (5).
2. If `det D_β ≠ 0`, then `β` is optimal iff all `det(D_β) P_i ≥ 0` and all `det(D_β) Q_j ≥ 0`.
3. `detPoly β` evaluates to `det D_β`.
4. If `m ≥ 2` and `det D_β ≠ 0`, the columns can be re-arranged to make the determinant positive, without
   changing whether `β` is optimal.
5. An optimal basis has an optimal basic solution of form (4).

**Formalization Note.** Clause 4 needs `m ≥ 2`: for `m ≤ 1` there is nothing to swap. Clause 2 covers
that case. -/
theorem display_5 {m n : ℕ} (β : Fin m ↪ Fin n) :
    (∀ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
      0 < (basisMatrix D β).det →
        (IsOptimalBasis D b c β ↔
          (∀ i, 0 ≤ MvPolynomial.eval (lpData D b c) (basicPoly β i)) ∧
          ∀ j, 0 ≤ MvPolynomial.eval (lpData D b c) (reducedPoly β j))) ∧
    (∀ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
      (basisMatrix D β).det ≠ 0 →
        (IsOptimalBasis D b c β ↔
          (∀ i, 0 ≤ (basisMatrix D β).det * MvPolynomial.eval (lpData D b c) (basicPoly β i)) ∧
          ∀ j, 0 ≤ (basisMatrix D β).det * MvPolynomial.eval (lpData D b c) (reducedPoly β j))) ∧
    (∀ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
      MvPolynomial.eval (lpData D b c) (detPoly β) = (basisMatrix D β).det) ∧
    (∀ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
      2 ≤ m → (basisMatrix D β).det ≠ 0 →
        ∃ σ : Equiv.Perm (Fin m),
          0 < (basisMatrix D (σ.toEmbedding.trans β)).det ∧
          (IsOptimalBasis D b c (σ.toEmbedding.trans β) ↔ IsOptimalBasis D b c β)) ∧
    (∀ (D : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ),
      IsOptimalBasis D b c β → StdOptimal D b c (basicSolution D b β)) := by sorry

end EnvelopeMSLP
