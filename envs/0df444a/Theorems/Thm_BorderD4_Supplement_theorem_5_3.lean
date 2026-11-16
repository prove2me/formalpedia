-- Prove2me | Theorems.Thm_BorderD4_Supplement_theorem_5_3
-- name    : BorderD4.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:03:10.738355+00:00
-- url     : https://prove2.me/theorems/d46c67d4-f63c-4f15-aa20-ce926e31e6c1
-- title:
--   Theorem 5.3 — exact low-weight translation
-- statement:
--   Let $F$ be an algebraically closed field of characteristic $0$. Let $k,\delta\ge1$, $n>k\delta^k$ and $N=(k+1)n$. Suppose
--   $$P_{k+1,n}=\sum_{i=1}^k T_i,$$
--   where each $T_i$ is a product of nonzero polynomials in $F[x]$ of degree at most $\delta$, and $\sum_{i=1}^k\deg T_i\le D$. Then there exist integers $m,t_0,k'$ with
--   $$N-2k\le m\le N,\qquad 0\le t_0\le\min\{2k\delta^{2k},n\},\qquad 1\le k'\le k,$$
--   elements $b_1,\dots,b_{t_0}\in F$ and polynomials $Q_a\in F[x_1,\dots,x_m,x_a]$ for $m<a\le N$ such that:
--
--   1. each $Q_a$ is irreducible of degree at most $\delta^k$, with $Q_a(0)=0$ and $(\partial_{x_a}Q_a)(0)\ne0$, and the natural map $F[[x_1,\dots,x_m]]\to F[[x]]/\langle Q_{m+1},\dots,Q_N\rangle$ is an isomorphism;
--   2. in $F[[x]]/\langle Q_{m+1},\dots,Q_N\rangle$,
--   $$\prod_{t=1}^{t_0}(x_t+b_t)\cdot\prod_{t=t_0+1}^{n}x_t=\sum_{i=1}^{k'}T'_i,$$
--   where each $T'_i$ is a product of polynomials in $F[x]$ of degree at most $\delta$, none of which vanishes at $0$, and $\sum_{i=1}^{k'}\deg T'_i\le D$.
--
--   The theorem turns a hypothetical exact circuit for $P_{k+1,n}$ into a computation of a shifted block monomial by at most $k$ product gates that are units at the origin, after shifting at most $2k\delta^{2k}$ coordinates. It is the exact counterpart of the border low-weight translation, Theorem 6.7.
--
--   **Formalization Note** Variables are $\mathrm{Fin}\,N$ with $x_i$ at index $i-1$. A product of polynomials is a list of factors; degrees are total degrees.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_N, P_{k+1,n} with first block x_1, …, x_n → Fin N with x_i at index i − 1; P_{k+1,n} = `sumProductLin` (the published sumProduct renamed by (j,t) ↦ t + nj); reason: renaming of variables; block 1 is x_1, …, x_n as on the page
--   - encoding: T_i a product of polynomials; deg → a list of factors and its product; total degree; reason: a finite product is the product of a list
--   - encoding: Q_a ∈ F[x_1, …, x_m, x_a] irreducible → Q_a ∈ F[x] with vars Q_a ⊆ {x_1, …, x_m, x_a}, irreducible in F[x]; reason: F[x_1..x_m,x_a] ⊆ F[x] is a polynomial subring and irreducibility is the same in both
--   - encoding: b_1, …, b_{t0} and Q_a for m < a ≤ N → total functions b : Fin N → F and Q : Fin N → F[x], of which only b_t (t < t0) and Q_a (a ≥ m, 0-based) are used; reason: existential witnesses; unused values are unconstrained
--   - encoding: N − 2k ≤ m ≤ N → N ≤ m + 2k and m ≤ N; reason: avoids truncated natural-number subtraction; equal as integers
--   - encoding: the natural map F[[x_1..x_m]] → F[[x]]/⟨Q_{m+1}, …, Q_N⟩ is an isomorphism → the ring hom MvPowerSeries.rename (Fin m ↪ Fin N) followed by the quotient by the ideal of F[[x]] spanned by the Q_a as power series is bijective; reason: a bijective ring homomorphism is an isomorphism
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 5.3, p.47; standing assumption of §5, p.46; Lemma 4.14, p.43

import Mathlib
import Definitions.Def_BorderD4_Supplement_sumProductLin
set_option autoImplicit false

open MvPolynomial

namespace BorderD4.Supplement

/-- Theorem 5.3: exact low-weight translation.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Theorem 5.3, p.47; standing assumption of §5, p.46 (`F` algebraically closed of characteristic `0`); Lemma 4.14, p.43.

Let `k, δ ≥ 1`, `n > kδ^k`, `N := (k+1)n`. Suppose `P_{k+1,n} = ∑_{i=1}^k T_i`, each `T_i` a product of nonzero
polynomials of degree at most `δ`, and `∑_i deg T_i ≤ D`. Then there are integers `m, t_0, k'`, elements
`b_1, …, b_{t_0} ∈ F` and polynomials `Q_a ∈ F[x_1, …, x_m, x_a]` (`m < a ≤ N`) with `N − 2k ≤ m ≤ N`,
`0 ≤ t_0 ≤ min{2kδ^{2k}, n}`, `1 ≤ k' ≤ k`, such that
1. each `Q_a` is irreducible of degree at most `δ^k`, `Q_a(0) = 0`, `(∂_{x_a} Q_a)(0) ≠ 0`, and the natural map
   `F[[x_1, …, x_m]] → F[[x]]/⟨Q_{m+1}, …, Q_N⟩` is an isomorphism;
2. in `F[[x]]/⟨Q_{m+1}, …, Q_N⟩`, `∏_{t=1}^{t_0}(x_t + b_t) · ∏_{t=t_0+1}^{n} x_t = ∑_{i=1}^{k'} T'_i`, where each `T'_i`
   is a product of polynomials of degree at most `δ`, none vanishing at `0`, and `∑_i deg T'_i ≤ D`.

**Formalization Note** Variables are `Fin N` with the page's `x_i` at index `i − 1` (`sumProductLin`), so
`x_1, …, x_m` are the indices `< m` and `m < a ≤ N` is `m ≤ a`. A product of polynomials is a list of factors and
its product; `deg` is the total degree. `Q_a ∈ F[x_1, …, x_m, x_a]` is `vars Q_a ⊆ {x_1, …, x_m, x_a}`;
irreducibility is in `F[x]`, equivalent to irreducibility in `F[x_1, …, x_m, x_a]`. `Q` and `b` are total functions
of which only `Q_a` for `a ≥ m` and `b_t` for `t < t_0` are used. `N − 2k ≤ m` is written `N ≤ m + 2k`. The ideal
`⟨Q_{m+1}, …, Q_N⟩` is generated in the power series ring `F[[x]]` by the `Q_a` viewed as power series, and the
natural map is `MvPowerSeries.rename` along `Fin m ↪ Fin N` followed by the quotient map; "is an isomorphism" is
bijectivity of this ring homomorphism. -/
theorem theorem_5_3 {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] (k δ n D : ℕ) (hk : 1 ≤ k) (hδ : 1 ≤ δ)
    (hn : k * δ ^ k < n) (T : Fin k → List (MvPolynomial (Fin ((k + 1) * n)) F))
    (hT : ∀ i, ∀ q ∈ T i, q ≠ 0 ∧ q.totalDegree ≤ δ)
    (hP : sumProductLin F k n = ∑ i, (T i).prod)
    (hD : ∑ i, ((T i).prod).totalDegree ≤ D) :
    ∃ (m : ℕ) (hm : m ≤ (k + 1) * n) (t₀ k' : ℕ) (b : Fin ((k + 1) * n) → F)
      (Q : Fin ((k + 1) * n) → MvPolynomial (Fin ((k + 1) * n)) F)
      (T' : Fin k' → List (MvPolynomial (Fin ((k + 1) * n)) F)),
      (k + 1) * n ≤ m + 2 * k ∧ t₀ ≤ min (2 * k * δ ^ (2 * k)) n ∧ 1 ≤ k' ∧ k' ≤ k ∧
      (∀ a : Fin ((k + 1) * n), m ≤ a.val →
        (Q a).vars ⊆ insert a (Finset.univ.filter fun i : Fin ((k + 1) * n) => i.val < m) ∧
        Irreducible (Q a) ∧ (Q a).totalDegree ≤ δ ^ k ∧ constantCoeff (Q a) = 0 ∧
        constantCoeff (pderiv a (Q a)) ≠ 0) ∧
      Function.Bijective
        ((Ideal.Quotient.mk (Ideal.span ((fun a => ((Q a : MvPolynomial (Fin ((k + 1) * n)) F) :
            MvPowerSeries (Fin ((k + 1) * n)) F)) '' {a | m ≤ a.val}))).comp
          (MvPowerSeries.rename (R := F) (Fin.castLE hm)).toRingHom) ∧
      Ideal.Quotient.mk (Ideal.span ((fun a => ((Q a : MvPolynomial (Fin ((k + 1) * n)) F) :
            MvPowerSeries (Fin ((k + 1) * n)) F)) '' {a | m ≤ a.val}))
          (((∏ t ∈ Finset.univ.filter (fun i : Fin ((k + 1) * n) => i.val < t₀), (X t + MvPolynomial.C (b t))) *
            ∏ t ∈ Finset.univ.filter (fun i : Fin ((k + 1) * n) => t₀ ≤ i.val ∧ i.val < n), X t :
              MvPolynomial (Fin ((k + 1) * n)) F) : MvPowerSeries (Fin ((k + 1) * n)) F) =
        Ideal.Quotient.mk (Ideal.span ((fun a => ((Q a : MvPolynomial (Fin ((k + 1) * n)) F) :
            MvPowerSeries (Fin ((k + 1) * n)) F)) '' {a | m ≤ a.val}))
          ((∑ i, (T' i).prod : MvPolynomial (Fin ((k + 1) * n)) F) : MvPowerSeries (Fin ((k + 1) * n)) F) ∧
      (∀ i, ∀ q ∈ T' i, q.totalDegree ≤ δ ∧ constantCoeff q ≠ 0) ∧
      ∑ i, ((T' i).prod).totalDegree ≤ D := by sorry

end BorderD4.Supplement
