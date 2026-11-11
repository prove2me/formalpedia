-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_lemma_3_5
-- name    : CorrBoundsPoly.ExactDegree.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:50.619605+00:00
-- url     : https://prove2.me/theorems/2d135060-bcaa-4c68-947e-f672b5854875
-- title:
--   Lemma 3.5 — pairing substitution $\sigma_{2D,m}=\sigma_{D,r}(u_1v_1,\dots,u_rv_r)$ in $A_m$ and the recurrence $a_{2D}(m)=\mathbb E\,a_D(K)$
-- statement:
--   For $m\ge0$ and $r=\lfloor m/2\rfloor$ put, for $1\le i\le r$,
--   $$u_i=x_{2i-1}+\sum_{j=2i+1}^m x_j,\qquad v_i=x_{2i}+\sum_{j=2i+1}^m x_j .$$
--   1. These linear forms, together with the leftover $x_m$ when $m$ is odd, form an invertible linear coordinate system.
--   2. In the truncated algebra $A_m$,
--   $$\sigma_{2D,m}(x)=\sigma_{D,r}(u_1v_1,\dots,u_rv_r). \tag{3.7}$$
--   3. Consequently, for every $D\ge1$,
--   $$a_{2D}(m)=\mathbb E_{K\sim\mathrm{Bin}(\lfloor m/2\rfloor,1/2)}\,a_D(K),\qquad a_1(m)=\mathbf 1\{m=0\}. \tag{3.8}$$
--
--   The recurrence (3.8) computes the rank defect of every dyadic elementary core from $a_1$; it is matched by the random-walk recurrence of Lemma 3.8.
--
--   Differences from the source:
--   - encoding: 1-based indices → 0-based (`pairU m i = X(2i) + ∑_{j≥2i+2} X j`, `pairV m i = X(2i+1) + ∑_{j≥2i+2} X j`, `i : Fin (m/2)`); reason: relabelling
--   - encoding: "invertible linear coordinate system" → the $m$ linear forms `pairCoord m` (the $u_i$, $v_i$ and the leftover $x_m$) are linearly independent; reason: $m$ independent linear forms in $m$ variables are exactly an invertible linear change of coordinates
--   - reading: (3.7) is stated without a range for $D$ → every $D\ge0$; reason: the page quantifies $D\ge1$ only for (3.8); at $D=0$ both sides are $1$
--   - encoding: $\mathbb E_{K\sim\mathrm{Bin}(r,1/2)}$ → the finite sum $\sum_{k=0}^r\binom rk2^{-r}(\cdot)$ (`binomExp`); reason: definition of the binomial law
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 27 (PDF 29), Lemma 3.5, Eqs. (3.7), (3.8)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Lemma 3.5** (Pairing and the exact recurrence; Xin Li, *More on Correlation Bounds for
Polynomials*, p. 27, PDF 29). With `r = ⌊m/2⌋`, `u_i = x_{2i−1} + ∑_{j=2i+1}^m x_j`,
`v_i = x_{2i} + ∑_{j=2i+1}^m x_j` (`1 ≤ i ≤ r`): (1) these linear forms, together with the leftover
`x_m` when `m` is odd, form an invertible linear coordinate system (`m` linearly independent linear
forms in `m` variables); (2) in `A_m`, `σ_{2D,m}(x) = σ_{D,r}(u_1v_1, …, u_rv_r)` (Eq. (3.7));
(3) for every `D ≥ 1`, `a_{2D}(m) = E_{K∼Bin(⌊m/2⌋,1/2)} a_D(K)`, and `a_1(m) = 1{m=0}`
(Eq. (3.8)). -/
theorem lemma_3_5 :
    (∀ m : ℕ, LinearIndependent (ZMod 2) (pairCoord m) ∧
      ∀ D : ℕ, toTrunc (sigma (2 * D) m) =
        toTrunc (MvPolynomial.aeval (fun i : Fin (m / 2) => pairU m i * pairV m i)
          (sigma D (m / 2)))) ∧
    (∀ D : ℕ, 1 ≤ D → ∀ m : ℕ, aD (2 * D) m = binomExp (m / 2) (fun k => aD D k)) ∧
    (∀ m : ℕ, aD 1 m = if m = 0 then 1 else 0) := by sorry

end CorrBoundsPoly.ExactDegree
