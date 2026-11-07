-- Prove2me | Theorems.Thm_DetANN_eq_27
-- name    : DetANN.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:33.140632+00:00
-- url     : https://prove2.me/theorems/8a96755d-0c25-4fcb-8d13-f607613acf6f
-- title:
--   (27), p.18 — $\min_v\|q-x_v\|\le\frac{\alpha+\sqrt{2\alpha^2\kappa+12\tau(1+\alpha)^2}}{\sqrt{1-\tau}}\,r$ for any tuple family with $\mathbb E_I\|a_I-a\|^2\le\kappa\mathcal V$
-- statement:
--   Throughout, a **tuple family** is a map $S:\mathcal V\times\mathcal O\to[d]$ on finite nonempty sets $\mathcal V$ (tuples) and $\mathcal O$ (occurrences) with **uniform block frequencies**: every block $i\in[d]$ occurs $|\mathcal V||\mathcal O|/d$ times among the pairs $(v,o)$. Choose $(V,O)$ uniformly and put $I=S(V,O)$. For answers $x_v\in P$ and a point $x^\star\in P$ write $a_i=\mathbb E[x_V-x^\star\mid I=i]$, $a=\mathbb E[x_V-x^\star]$, $\mathcal V=\mathbb E\|x_V-x^\star-a_I\|_2^2$, $r=\|q-x^\star\|_2$, and $\|\mathcal A_vz\|_2^2=\sum_{o}\|A_{S(v,o)}z\|_2^2$ for the superblock of $v$ (repeated blocks counted with multiplicity). The **local guarantee** with factor $\alpha$ is $\|\mathcal A_v(q-x_v)\|_2\le\alpha\min_{y\in P}\|\mathcal A_v(q-y)\|_2$ for every $v$.
--
--   Let $A_1,\dots,A_d$ be a $\tau$-balanced block system for $P$ with $0<\tau<1$, let the answers $x_v\in P$ satisfy the local guarantee with factor $\alpha\ge1$, let $x^\star\in P$, and let $\kappa\ge0$ satisfy $\mathbb E_I\|a_I-a\|_2^2\le\kappa\,\mathcal V$. Then
--
--   $$\sqrt{\mathbb E_V\|q-x_V\|_2^2}\le\frac{\alpha+\sqrt{2\alpha^2\kappa+12\tau(1+\alpha)^2}}{\sqrt{1-\tau}}\,r ,$$
--
--   and therefore some tuple $v$ has $\|q-x_v\|_2$ at most the same bound.
--
--   With $\kappa=\rho^2/(1-\rho^2)$ from Lemma 7.2 this is (27) for the walk family; with $\kappa=1/(s-1)$ from Lemma 5.1 it is Theorem 4.1 for the exhaustive family.
--
--   Differences from the source:
--   - generalization: the walk family of §7 (and, in §5, the exhaustive family [d]^s); x⋆ a nearest neighbor of q → any finite tuple family with uniform block frequencies and nonempty Vtx, Occ; x⋆ any point of P; reason: §7.3 says the arguments use only uniform block frequencies and balance of differences; both families have uniform frequencies, and a nearest neighbor is a point of P
--   - encoding: expectations over the random choice of V and of an occurrence; the min-form local guarantee (11)/(25) → finite uniform averages over Vtx × Occ; the squared guarantee ‖𝒜_v(q − x_v)‖² ≤ α²‖𝒜_v(q − y)‖² for all y ∈ P; reason: the averages are the expectations; for α ≥ 0 and finite nonempty P the squared and min forms are equivalent
--   - generalization: κ = ρ²/(1 − ρ²) via Lemma 7.2 → any κ ≥ 0 with E_I‖a_I − a‖² ≤ κ𝒱 as a hypothesis; reason: Lemma 7.2 supplies the hypothesis with κ = ρ²/(1 − ρ²), which gives the printed (27)
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), (27), §7.3, p.18 (PDF p.18); exhaustive case: Theorem 4.1, p.8

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **(27), in the general form** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.3, p.18).
Let `A₁, …, A_d` be a `τ`-balanced block system for `P`, let the answers `x_v ∈ P` satisfy the local
guarantee with factor `α ≥ 1`, let `x⋆ ∈ P` and `r = ‖q − x⋆‖`, and suppose
`E_I ‖a_I − a‖² ≤ κ 𝒱` with `κ ≥ 0`. Then
`√(E_V ‖q − x_V‖²) ≤ (α + √(2α²κ + 12τ(1 + α)²))/√(1 − τ) · r`, and some tuple `v` has
`‖q − x_v‖` at most the same bound.

The paper's (27) is the case `κ = ρ²/(1 − ρ²)` (Lemma 7.2); Theorem 4.1 is the case `κ = 1/(s − 1)`
(Lemma 5.1).

**Formalization Note.** The family is any finite family of tuples `S : Vtx → Occ → Fin d` with
uniform block frequencies and nonempty `Vtx`, `Occ` (the paper: the exhaustive family `[d]^s` of §5
and the walk family of §7). Expectations are finite averages over `(V, O)` uniform on `Vtx × Occ`
(see `DetANN.TupleFamily`). `x⋆` is any point of `P`; the paper takes a nearest neighbor of `q`, and
the argument uses only `x⋆ ∈ P`. -/
theorem eq_27 {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ] [Nonempty Vtx] [Nonempty Occ]
    (τ α : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα : 1 ≤ α)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (q xs : EuclideanSpace ℝ (Fin d)) (hxs : xs ∈ P)
    (x : Vtx → EuclideanSpace ℝ (Fin d)) (hx : ∀ v, x v ∈ P)
    (hloc : LocalGuarantee A S P q x α)
    (κ : ℝ) (hκ : 0 ≤ κ) (hκV : betweenVar S x xs ≤ κ * withinVar S x xs) :
    Real.sqrt ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖q - x v‖ ^ 2) ≤
        (α + Real.sqrt (2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2)) / Real.sqrt (1 - τ) * ‖q - xs‖ ∧
      ∃ v : Vtx, ‖q - x v‖ ≤
        (α + Real.sqrt (2 * α ^ 2 * κ + 12 * τ * (1 + α) ^ 2)) / Real.sqrt (1 - τ) * ‖q - xs‖ := by sorry

end DetANN
