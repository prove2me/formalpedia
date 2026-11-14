-- Prove2me | Theorems.Thm_DetANN_eq_26
-- name    : DetANN.eq_26
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:26:26.179361+00:00
-- url     : https://prove2.me/theorems/bf9f92ae-8826-4206-8352-4bbe9f3c1357
-- title:
--   (26), p.18 (Lemma 5.2 form) — $\sum_iT_i+(1-\tau)\mathcal V\le\alpha^2r^2$ for any tuple family
-- statement:
--   Throughout, a **tuple family** is a map $S:\mathcal V\times\mathcal O\to[d]$ on finite nonempty sets $\mathcal V$ (tuples) and $\mathcal O$ (occurrences) with **uniform block frequencies**: every block $i\in[d]$ occurs $|\mathcal V||\mathcal O|/d$ times among the pairs $(v,o)$. Choose $(V,O)$ uniformly and put $I=S(V,O)$. For answers $x_v\in P$ and a point $x^\star\in P$ write $a_i=\mathbb E[x_V-x^\star\mid I=i]$, $a=\mathbb E[x_V-x^\star]$, $\mathcal V=\mathbb E\|x_V-x^\star-a_I\|_2^2$, $r=\|q-x^\star\|_2$, and $\|\mathcal A_vz\|_2^2=\sum_{o}\|A_{S(v,o)}z\|_2^2$ for the superblock of $v$ (repeated blocks counted with multiplicity). The **local guarantee** with factor $\alpha$ is $\|\mathcal A_v(q-x_v)\|_2\le\alpha\min_{y\in P}\|\mathcal A_v(q-y)\|_2$ for every $v$.
--
--   Let $A_1,\dots,A_d$ be a $\tau$-balanced block system for $P$ with $0<\tau<1$, let the answers $x_v\in P$ satisfy the local guarantee with factor $\alpha\ge1$, let $x^\star\in P$, and put $T_i=\|A_i(q-x^\star-a_i)\|_2^2$. Then
--
--   $$\sum_{i=1}^dT_i+(1-\tau)\mathcal V\le\alpha^2r^2,\qquad\mathcal V\le\frac{\alpha^2r^2}{1-\tau},\qquad\sum_{i=1}^dT_i+\mathcal V\le\frac{\alpha^2r^2}{1-\tau}.$$
--
--   This bounds the projected error and the within-block variance; it is (26) for the walk family and (17)–(18) of Lemma 5.2 for the exhaustive family.
--
--   Differences from the source:
--   - generalization: the walk family of §7 (and, in §5, the exhaustive family [d]^s); x⋆ a nearest neighbor of q → any finite tuple family with uniform block frequencies and nonempty Vtx, Occ; x⋆ any point of P; reason: §7.3 says the arguments use only uniform block frequencies and balance of differences; both families have uniform frequencies, and a nearest neighbor is a point of P
--   - encoding: expectations over the random choice of V and of an occurrence; the min-form local guarantee (11)/(25) → finite uniform averages over Vtx × Occ; the squared guarantee ‖𝒜_v(q − x_v)‖² ≤ α²‖𝒜_v(q − y)‖² for all y ∈ P; reason: the averages are the expectations; for α ≥ 0 and finite nonempty P the squared and min forms are equivalent
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), (26), §7.3, p.18 (PDF p.18); Lemma 5.2, (17)–(18), p.11

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **(26), the Lemma 5.2 form** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.3, p.18; Lemma 5.2, (17)–(18), p.11).
With `T_i = ‖A_i(q − x⋆ − a_i)‖²` and `r = ‖q − x⋆‖`:
`∑_i T_i + (1 − τ)𝒱 ≤ α² r²`; in particular `𝒱 ≤ α² r²/(1 − τ)` and `∑_i T_i + 𝒱 ≤ α² r²/(1 − τ)`.

**Formalization Note.** The family is any finite family of tuples `S : Vtx → Occ → Fin d` with
uniform block frequencies and nonempty `Vtx`, `Occ` (the paper: the exhaustive family `[d]^s` of §5
and the walk family of §7). Expectations are finite averages over `(V, O)` uniform on `Vtx × Occ`
(see `DetANN.TupleFamily`). `x⋆` is any point of `P`; the paper takes a nearest neighbor of `q`, and
the argument uses only `x⋆ ∈ P`. -/
theorem eq_26 {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ] [Nonempty Vtx] [Nonempty Occ]
    (τ α : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα : 1 ≤ α)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (q xs : EuclideanSpace ℝ (Fin d)) (hxs : xs ∈ P)
    (x : Vtx → EuclideanSpace ℝ (Fin d)) (hx : ∀ v, x v ∈ P)
    (hloc : LocalGuarantee A S P q x α) :
    ∑ i, ‖A i (q - xs - condMean S x xs i)‖ ^ 2 + (1 - τ) * withinVar S x xs ≤
        α ^ 2 * ‖q - xs‖ ^ 2 ∧
      withinVar S x xs ≤ α ^ 2 * ‖q - xs‖ ^ 2 / (1 - τ) ∧
      ∑ i, ‖A i (q - xs - condMean S x xs i)‖ ^ 2 + withinVar S x xs ≤
        α ^ 2 * ‖q - xs‖ ^ 2 / (1 - τ) := by sorry

end DetANN
