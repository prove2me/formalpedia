-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_7
-- name    : BorderDiffEq.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:25:25.056761+00:00
-- url     : https://prove2.me/theorems/821be269-a8a2-494e-ae08-f72cd3ec8011
-- title:
--   Lemma 4.7 — Waring rank of $\prod_{j=1}^m\ell_j^{d_j}$ is at most $d^m$ (corrected: excludes $d=0<m$)
-- statement:
--   Let $K$ be a field of characteristic zero and $\ell_1,\dots,\ell_m$ linear forms (homogeneous of degree one) over $K$. Let $d_1,\dots,d_m\in\mathbb N$, $d=\sum_jd_j$, and assume $m=0$ or $d\ge1$. Then there are scalars $\alpha_i\in K$ and linear forms $L_i$, $1\le i\le d^m$, with
--   $$
--   \prod_{j=1}^m\ell_j^{\,d_j}=\sum_{i=1}^{d^m}\alpha_i\,L_i^{\,d},
--   $$
--   that is, $\mathrm{WR}\big(\prod_j\ell_j^{d_j}\big)\le d^m$.
--
--   The bound turns the products of affine forms that appear when one expands determinants of logarithmic derivatives into sums of powers (Lemma 5.3, Proposition 5.4, Theorem 2.1).
--
--   **Formalization Note** The Waring rank is the homogeneous one of §4.2, stated as an explicit decomposition with exactly $d^m$ summands (zero coefficients pad a shorter one). The zero polynomial counts as a linear form; this is harmless.
--
--   Differences from the source:
--   - correction: no condition on $d_1,\dots,d_m$ → $m=0$ or $d=\sum_jd_j\ge1$; reason: for $m\ge1$ and all $d_j=0$ the product is $1$, and the printed bound claims $\mathrm{WR}(1)\le0^m=0$, false since $1\ne0$; exactly this case is excluded (if some $d_j=0$ but $d\ge1$, dropping those forms gives the bound $d^{m'}\le d^m$)
--   - encoding: $\mathrm{WR}(f)\le d^m$ → an explicit decomposition with $d^m$ summands of homogeneous linear forms; reason: the definition of Waring rank in §4.2, padded with zero coefficients
--   - encoding: $n$ variables $x_1,\dots,x_n$ → variables indexed by an arbitrary type $\sigma$; reason: the number of variables plays no role; finitely many variables is the case $\sigma=$ `Fin n`
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.7, p.27 (Waring rank: §4.2, p.26)

import Mathlib

namespace BorderDiffEq

/-- **Lemma 4.7 (Waring rank of a product of linear forms)** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.7, p.27; Waring rank defined in §4.2, p.26). Let `f = ∏_{j=1}^m ℓⱼ^{dⱼ}` be a
product of linear forms with `∑ⱼ dⱼ = d`. Then `WR(f) ≤ d^m`, i.e. `f = ∑_{i=1}^{d^m} αᵢ Lᵢ^d` for
some scalars `αᵢ` and linear forms `Lᵢ`.

**Formalization Note.** Over any field `K` of characteristic zero (the paper's arbitrary `F`;
applied over `F(y)` and `F(ε, y)`). Linear forms are homogeneous polynomials of degree 1
(`IsHomogeneous _ 1`; the zero polynomial is allowed and harmless), and the Waring rank is the
homogeneous one of §4.2, stated as an explicit decomposition with exactly `d^m` summands (zero
coefficients pad a shorter one). **Correction:** the printed statement is false when `d = 0` and
`m ≥ 1` (then `f = 1` and the bound claims `WR(1) ≤ 0^m = 0`); exactly that case is excluded by
`m = 0 ∨ 1 ≤ d`. -/
theorem lemma_4_7 (K : Type) [Field K] [CharZero K] (σ : Type) (m : ℕ)
    (ℓ : Fin m → MvPolynomial σ K) (hℓ : ∀ j, (ℓ j).IsHomogeneous 1)
    (dexp : Fin m → ℕ) (hd : m = 0 ∨ 1 ≤ ∑ j, dexp j) :
    ∃ (α : Fin ((∑ j, dexp j) ^ m) → K) (L : Fin ((∑ j, dexp j) ^ m) → MvPolynomial σ K),
      (∀ i, (L i).IsHomogeneous 1) ∧
      ∏ j, ℓ j ^ dexp j = ∑ i, MvPolynomial.C (α i) * L i ^ (∑ j, dexp j) := by sorry

end BorderDiffEq
