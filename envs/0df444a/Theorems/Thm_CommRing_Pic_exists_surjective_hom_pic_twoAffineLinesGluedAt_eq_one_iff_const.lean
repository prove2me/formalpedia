-- Prove2me | Theorems.Thm_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
-- name    : CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/777c25d2-87e7-5f85-9d2b-32d797aad235
-- title:
--   Picard group of two affine lines glued at rational points
-- statement:
--   Let $k$ be a field, let $\iota$ be a finite index type, and let $a, b \colon \iota \to k$ be injective. Let $R$ be the $k$-subalgebra of $k[X] \times k[X]$ defined as the equaliser of the two $k$-algebra maps $k[X] \times k[X] \to (\iota \to k)$ sending $(f,g)$ to $(f(a_i))_{i}$ and to $(g(b_i))_{i}$ respectively, i.e. $R = \{(f,g) : f(a_i) = g(b_i)\ \text{for all } i\}$. The assertion is that there exists a group homomorphism $\delta \colon (\iota \to k^\times) \to \operatorname{Pic}(R)$, from the group of $\iota$-tuples of units of $k$ under pointwise multiplication to the Picard group of $R$ in the sense of `CommRing.Pic`, such that: $\delta$ is surjective; for every $w$, $\delta w = 1$ holds precisely when $w$ is a constant family $i \mapsto c$ for some $c \in k^\times$; and for every $w$ there is an $R$-submodule $N$ of $k[X] \times k[X]$ whose elements are exactly the pairs $(f,g)$ with $f(a_i) = w_i\, g(b_i)$ for all $i$, together with an isomorphism of $R$-modules between the module underlying $\delta w$ and $N$. In particular $\operatorname{Pic}(R) \cong (k^\times)^{\iota}/k^\times$.
--
--   This is the line-bundle computation of the Picard group of the affine curve obtained by glueing two copies of $\mathbb{A}^1_k$ transversally at the finitely many rational points $a_i$ and $b_i$, exhibiting it as the $k$-points of a split torus of rank $\#\iota - 1$, with the explicit invertible modules $N_w$ of twisted glueing data. It is used by the two-chart glueing lemmas [`TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible`](thm.html#TwoChartCech.exists_linearEquiv_gluedLinesM0_of_invertible) and [`TwoChartCech.exists_linearEquiv_gluedLinesM1_of_invertible`](thm.html#TwoChartCech.exists_linearEquiv_gluedLinesM1_of_invertible), and rests on the Mayer–Vietoris (conductor square) boundary map [`CommRing.Pic.exists_boundaryHom_conductorSquare_exact`](thm.html#CommRing.Pic.exists_boundaryHom_conductorSquare_exact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u v

theorem CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
    {k : Type u} [Field k] {ι : Type v} [Finite ι] (a b : ι → k)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    let R : Subalgebra k (k[X] × k[X]) :=
      AlgHom.equalizer
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (a i)).comp (AlgHom.fst k k[X] k[X]))
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (b i)).comp (AlgHom.snd k k[X] k[X]))
    ∃ δ : (ι → kˣ) →* CommRing.Pic ↥R,
      Function.Surjective δ ∧
      (∀ w : ι → kˣ, δ w = 1 ↔ ∃ c : kˣ, w = Function.const ι c) ∧
      ∀ w : ι → kˣ, ∃ N : Submodule ↥R (k[X] × k[X]),
        (∀ p : k[X] × k[X], p ∈ N ↔ ∀ i, (p.1).eval (a i) = (w i : k) * (p.2).eval (b i)) ∧
        Nonempty ((δ w : CommRing.Pic ↥R) ≃ₗ[↥R] ↥N) := by sorry
