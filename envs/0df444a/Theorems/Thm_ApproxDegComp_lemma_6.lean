-- Prove2me | Theorems.Thm_ApproxDegComp_lemma_6
-- name    : ApproxDegComp.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:31:40.771073+00:00
-- url     : https://prove2.me/theorems/8fd7d9b3-ed42-4d26-b8c6-9e5993d456dd
-- title:
--   Lemma 6 — $\|\mathcal S(P)\|_{[-1,1]^n}\le4^r\|P\|_{[-1,1]^n}$ for homogeneous $P$ of degree $r$
-- statement:
--   Let $P$ be a real homogeneous polynomial of degree $r$ in $n$ variables. Then
--
--   $$\|\mathcal S(P)\|_{[-1,1]^n}\le4^r\,\|P\|_{[-1,1]^n},$$
--
--   where $\|P\|_K=\sup_{x\in K}|P(x)|$ and $\mathcal S$ is squarefree extraction (Definition 19).
--
--   Squarefree extraction can increase the sup norm only by a factor exponential in the degree, which the proof of Theorem 23 absorbs by the choice of the constant $32e$.
--
--   **Formalization Note** The sup norms are written as bounds: whenever $|P|\le M$ on $[-1,1]^n$, then $|\mathcal S(P)|\le4^rM$ on $[-1,1]^n$.
--
--   Differences from the source:
--   - encoding: ‖·‖_{[−1,1]ⁿ} sup norms → for every M bounding |P| on [−1,1]ⁿ, |S(P)| ≤ 4^r M on [−1,1]ⁿ; reason: equivalent formulation of the sup-norm inequality on the compact cube
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 6, p.16 (proof Appendix A, pp.41–42)

import Mathlib
import Definitions.Def_ApproxDegComp_sqfreePoly

namespace ApproxDegComp

/-- **Lemma 6 (Norm of squarefree extraction)**, p.16 (proof in Appendix A, pp.41–42).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 6, p.16: "Let P be a real homogeneous polynomial of degree r in n variables. Then,
‖S(P)‖_{[−1,1]ⁿ} ≤ 4^r ‖P‖_{[−1,1]ⁿ}."

**Formalization Note** The sup norm `‖P‖_K = sup_{x∈K} |P(x)|` (p.10) is written as a bound: every
`M` that bounds `|P|` on `[−1,1]ⁿ` gives the bound `4^r M` for `|S(P)|` there; this is
equivalent since `[−1,1]ⁿ` is compact. -/
theorem lemma_6 (n r : ℕ) (P : MvPolynomial (Fin n) ℝ) (hP : P.IsHomogeneous r) (M : ℝ)
    (hM : ∀ x : Fin n → ℝ, (∀ i, |x i| ≤ 1) → |MvPolynomial.eval x P| ≤ M) :
    ∀ y : Fin n → ℝ, (∀ i, |y i| ≤ 1) →
      |MvPolynomial.eval y (sqfreePoly P)| ≤ 4 ^ r * M := by sorry

end ApproxDegComp
