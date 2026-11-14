-- Prove2me | Theorems.Thm_DetANN_lemma_5_3
-- name    : DetANN.lemma_5_3
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:26:23.998851+00:00
-- url     : https://prove2.me/theorems/e41a33b0-44cc-4b4c-b0cd-cb71fdd0d24f
-- title:
--   Lemma 5.3, p.12 (§7.3 form) — $\sum_i\|A_i(a_i-a)\|^2\le\mathbb E_I\|a_I-a\|^2+12\tau\,\mathbb E_V\|x_V-x^\star\|^2$
-- statement:
--   Throughout, a **tuple family** is a map $S:\mathcal V\times\mathcal O\to[d]$ on finite nonempty sets $\mathcal V$ (tuples) and $\mathcal O$ (occurrences) with **uniform block frequencies**: every block $i\in[d]$ occurs $|\mathcal V||\mathcal O|/d$ times among the pairs $(v,o)$. Choose $(V,O)$ uniformly and put $I=S(V,O)$. For answers $x_v\in P$ and a point $x^\star\in P$ write $a_i=\mathbb E[x_V-x^\star\mid I=i]$, $a=\mathbb E[x_V-x^\star]$, $\mathcal V=\mathbb E\|x_V-x^\star-a_I\|_2^2$, $r=\|q-x^\star\|_2$, and $\|\mathcal A_vz\|_2^2=\sum_{o}\|A_{S(v,o)}z\|_2^2$ for the superblock of $v$ (repeated blocks counted with multiplicity). The **local guarantee** with factor $\alpha$ is $\|\mathcal A_v(q-x_v)\|_2\le\alpha\min_{y\in P}\|\mathcal A_v(q-y)\|_2$ for every $v$.
--
--   Let $A_1,\dots,A_d$ be a $\tau$-balanced block system for $P$ with $0<\tau<1$, let $x_v\in P$ for every $v$, and let $x^\star\in P$. Then
--
--   $$\sum_{i=1}^d\|A_i(a_i-a)\|_2^2\le\mathbb E_I\|a_I-a\|_2^2+12\tau\,\mathbb E_V\|x_V-x^\star\|_2^2 .$$
--
--   It extends block balance from differences of database points to differences of their averages, which is what allows replacing $a_i$ by $a$.
--
--   Differences from the source:
--   - generalization: the walk family of §7 (and, in §5, the exhaustive family [d]^s); x⋆ a nearest neighbor of q → any finite tuple family with uniform block frequencies and nonempty Vtx, Occ; x⋆ any point of P; reason: §7.3 says the arguments use only uniform block frequencies and balance of differences; both families have uniform frequencies, and a nearest neighbor is a point of P
--   - encoding: expectations over the random choice of V and of an occurrence; the min-form local guarantee (11)/(25) → finite uniform averages over Vtx × Occ; the squared guarantee ‖𝒜_v(q − x_v)‖² ≤ α²‖𝒜_v(q − y)‖² for all y ∈ P; reason: the averages are the expectations; for α ≥ 0 and finite nonempty P the squared and min forms are equivalent
--   - generalization: x_v the answers of the local structures (satisfying (11)/(25)) → x_v any points of P; no local guarantee assumed; reason: the argument uses only (9), uniform frequencies and x_v, x⋆ ∈ P; the answers are points of P
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §7.3, p.18 (PDF p.18); Lemma 5.3, p.12

import Mathlib
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_TupleFamily

namespace DetANN

/-- **Lemma 5.3, in the §7.3 form** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §7.3, p.18; Lemma 5.3, p.12).
`∑_i ‖A_i(a_i − a)‖² ≤ E_I ‖a_I − a‖² + 12τ E_V ‖x_V − x⋆‖²`.

**Formalization Note.** The family is any finite family of tuples `S : Vtx → Occ → Fin d` with
uniform block frequencies and nonempty `Vtx`, `Occ` (the paper: the exhaustive family `[d]^s` of §5
and the walk family of §7). Expectations are finite averages over `(V, O)` uniform on `Vtx × Occ`
(see `DetANN.TupleFamily`). `x⋆` is any point of `P`; the paper takes a nearest neighbor of `q`, and
the argument uses only `x⋆ ∈ P`. The local guarantee is not used by
the argument (only block balance (9), uniform frequencies and `x_v, x⋆ ∈ P` are) and is not assumed. -/
theorem lemma_5_3 {d b : ℕ} {Vtx Occ : Type} [Fintype Vtx] [Fintype Occ] [Nonempty Vtx] [Nonempty Occ]
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (P : Finset (EuclideanSpace ℝ (Fin d)))
    (A : Fin d → EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin b))
    (hA : IsBalancedBlockSystem τ P A)
    (S : Vtx → Occ → Fin d) (hS : UniformFreq S)
    (q xs : EuclideanSpace ℝ (Fin d)) (hxs : xs ∈ P)
    (x : Vtx → EuclideanSpace ℝ (Fin d)) (hx : ∀ v, x v ∈ P) :
    ∑ i, ‖A i (condMean S x xs i - mean x xs)‖ ^ 2 ≤
      betweenVar S x xs + 12 * τ * ((Fintype.card Vtx : ℝ)⁻¹ * ∑ v, ‖x v - xs‖ ^ 2) := by sorry

end DetANN
