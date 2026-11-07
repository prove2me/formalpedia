-- Prove2me | Theorems.Thm_DoublingMST_lemma_2_7
-- name    : DoublingMST.lemma_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:43.136892+00:00
-- url     : https://prove2.me/theorems/63b85f5d-9036-4801-8358-30ba67e8ccea
-- title:
--   Lemma 2.7 — descendants pack and cover a local ball
-- statement:
--   Assume $|X|\ge2$, minimum interpoint distance $>1$, and let $N$ be a net hierarchy (§2.1). Let $u\in N_\ell$ be a level-$\ell$ net point. Then:
--
--   1. for every level $k<\ell$: $D_k(u)\subseteq B(u,2^{\ell+2})$, $D_k(u)$ is $2^{k-3}$-packing, and for every $x\in B(u,2^\ell)$ there is $v\in D_k(u)$ with $d(x,v)\le2^{k-2}$;
--   2. for $k=\ell$: $D_\ell(u)\subseteq B(u,2^{\ell+2})$, $D_\ell(u)$ is $2^{\ell-3}$-packing, and for every $x\in B(u,2^\ell)$ there is $v\in D_\ell(u)$ with $d(x,v)\le2^\ell$.
--
--   The lemma says that the descendants of a net point form a net of the ball around it at every finer scale.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: the §2.1 standing assumption that the minimum interpoint distance of X is greater than 1 (p.12) → hypothesis MinDistGtOne d; reason: the source assumes it throughout §§2.1–4 (it is what makes level-0 balls singletons)
--   - encoding: every integer k < ℓ → every natural number k < ℓ; reason: levels are 0, …, L, so D_k(u) is defined for k ≥ 0 only
--   - encoding: D_k(u) is 2^{k−3}-packing for B(u, 2^{ℓ+2}) → D_k(u) ⊆ B(u, 2^{ℓ+2}) and IsPacking with radius 2^{k−3}; reason: Definition 2.3's "packing for" is containment plus packing
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 2.7, p.13 (PDF p.15); proof p.48 (PDF p.50)

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ball
import Definitions.Def_DoublingMST_descendants
open scoped Classical

namespace DoublingMST

/-- **Lemma 2.7 (packing and covering by descendants).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 2.7, p.13 (PDF p.15): "Let u ∈ N_ℓ be a level-ℓ net point. Then for every integer
k < ℓ, (1) Packing: D_k(u) ⊆ B(u, 2^{ℓ+2}), and D_k(u) is 2^{k−3}-packing for B(u, 2^{ℓ+2}).
(2) Covering: for every x ∈ B(u, 2^ℓ), there exists v ∈ D_k(u), such that d(x, v) ≤ 2^{k−2}. For
k = ℓ, the packing and containment statement still holds, and covering holds with radius 2^ℓ."

Under the standing assumptions of §2.1 (a metric on `n ≥ 2` points with minimum interpoint distance
`> 1`, and a net hierarchy `H` with `L = ⌈log ∆⌉ + 4`), for every level `ℓ ≤ L` and `u ∈ N_ℓ`:
1. for every level `k < ℓ`: `D_k(u) ⊆ B(u, 2^{ℓ+2})`, `D_k(u)` is `2^{k−3}`-packing, and every
   `x ∈ B(u, 2^ℓ)` has some `v ∈ D_k(u)` with `d(x, v) ≤ 2^{k−2}`;
2. for `k = ℓ`: `D_ℓ(u) ⊆ B(u, 2^{ℓ+2})`, it is `2^{ℓ−3}`-packing, and every `x ∈ B(u, 2^ℓ)` has
   some `v ∈ D_ℓ(u)` with `d(x, v) ≤ 2^ℓ`.

**Formalization Note.** Levels are natural numbers, so `k` ranges over `0, …, ℓ − 1`; exponents
`k − 3`, `k − 2` are integers (`zpow`). "2^{k−3}-packing for B(u, 2^{ℓ+2})" is containment in the
ball plus the packing property. -/
theorem lemma_2_7 : ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d → MinDistGtOne d →
    ∀ (H : NetHierarchy d) (ℓ : ℕ), ℓ ≤ topLevel d → ∀ u ∈ H.N ℓ,
      (∀ k : ℕ, k < ℓ →
        (descendants H (u, ℓ) k ⊆ ball d u ((2 : ℝ) ^ (ℓ + 2)) ∧
          IsPacking d (descendants H (u, ℓ) k) ((2 : ℝ) ^ ((k : ℤ) - 3))) ∧
        ∀ x ∈ ball d u ((2 : ℝ) ^ ℓ), ∃ v ∈ descendants H (u, ℓ) k,
          d x v ≤ (2 : ℝ) ^ ((k : ℤ) - 2)) ∧
      (descendants H (u, ℓ) ℓ ⊆ ball d u ((2 : ℝ) ^ (ℓ + 2)) ∧
        IsPacking d (descendants H (u, ℓ) ℓ) ((2 : ℝ) ^ ((ℓ : ℤ) - 3)) ∧
        ∀ x ∈ ball d u ((2 : ℝ) ^ ℓ), ∃ v ∈ descendants H (u, ℓ) ℓ, d x v ≤ (2 : ℝ) ^ ℓ) := by sorry

end DoublingMST
