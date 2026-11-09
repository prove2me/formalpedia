-- Prove2me | Theorems.Thm_CondGeoVerif_lemma_B_2
-- name    : CondGeoVerif.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:35:33.277896+00:00
-- url     : https://prove2.me/theorems/f2d7be7f-548b-4d35-820c-ff7d112a1207
-- title:
--   Lemma B.2 — measurable near-optimal allocations
-- statement:
--   Let $k\ge1$, $0<\eta<1/2$, $f,g:\mathbb R^k\to\{-1,1\}$ Borel, $A$ a contraction and $j\in\{0,1\}$. For every $\xi>0$ there is a jointly measurable $e:\mathbb R^k\times\mathbb R^k\to[0,1]$ such that, for every $u$, $e(u,\cdot)\in\mathcal E_j$ and
--   $$\mathbb E_G[e(u,G)D_{f,g,A}(u,G)]\ge M_{j,\eta}(D_{f,g,A}(u,\cdot))-\xi .$$
--   The functions $u\mapsto M_{j,\eta}(D_{f,g,A}(u,\cdot))$ are measurable. Here $\mathcal E_0=\{0\le e\le1,\ \mathbb Ee=\eta\}$ and $\mathcal E_1$ adds $\mathbb E[Ge(G)]=0$.
--
--   The measurability clause shows that the envelopes $J_j$ are genuine expectations.
--
--   Differences from the source:
--   - generalization: the fixed-rule disagreement D_A(u, g) = 1{f(Aᵀu + B_A g) ≠ f(u)} → the family disagreement D_{f,g,A} of two Borel rules; reason: D_A is the case g = f; the family form is used in the proof of Theorem A.5
--   - encoding: E_j ⊆ L²(γ_k) → Borel functions with values in [0, 1] everywhere satisfying the constraints; reason: every element has such a representative
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Lemma B.2, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_CondGeoVerif_Jprog

set_option autoImplicit false

open MeasureTheory

namespace CondGeoVerif

/-- **Lemma B.2 (Measurable near-optimal allocations)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §B.1, p.25 = PDF p.28).
For every `ξ > 0`, fixed contraction `A` and `j ∈ {0, 1}`, there is a jointly measurable
`e : ℝᵏ × ℝᵏ → [0, 1]` such that, for every `u`, `e(u, ·) ∈ E_j` and
`E_G[e(u, G)D_A(u, G)] ≥ M_{j,η}(D_A(u, ·)) − ξ`. The functions `u ↦ M_{j,η}(D_A(u, ·))` are
measurable. Here `E₀ = {0 ≤ e ≤ 1, Ee = η}` and `E₁` adds `E[Ge(G)] = 0`.

**Formalization Note** Stated for the family disagreement `D_{f,g,A}` of two Borel rules (used in
Theorem A.5); the fixed-rule `D_A` is the case `g = f`. Membership in `errorAllocs j η k` gives the
values in `[0, 1]` and the moment constraints. -/
theorem lemma_B_2 {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1 / 2)
    (f g : Vec k → Bool) (hf : Measurable f) (hg : Measurable g) (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : IsContraction A) (j : Fin 2) (ξ : ℝ) (hξ : 0 < ξ) :
    (∃ e : Vec k → Vec k → ℝ, Measurable (fun p : Vec k × Vec k => e p.1 p.2) ∧
      ∀ u, e u ∈ errorAllocs j η k ∧
        Mprog j η (Dfga f g A u) - ξ ≤ ∫ z, e u z * ind (Dfga f g A u z) ∂(gauss k)) ∧
    Measurable (fun u => Mprog j η (Dfga f g A u)) := by sorry

end CondGeoVerif
