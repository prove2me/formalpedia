-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_8
-- name    : AGProxGap.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:38.819205+00:00
-- url     : https://prove2.me/theorems/58cb2d49-082e-47d6-8394-3a02a99cec56
-- title:
--   Lemma 3.8 — $a$ close points of a curve give interleaved distance $\le\frac{a}{a-\ell}e$
-- statement:
--   Let $\ell\ge 1$, $e\ge0$, $u_0,\dots,u_\ell\in\mathbb F_q^n$ with $r(z)=\sum_ju_jz^j$, let $a\ge\ell+1$ and $c_0,\dots,c_\ell\in\mathbb F_q^n$. Suppose there are pairwise distinct $z_1,\dots,z_a\in\mathbb F_q$ with
--   $$
--   d\Bigl(r(z_h),\sum_{j=0}^{\ell}c_jz_h^j\Bigr)\le e\qquad\text{for every } h\in[a].
--   $$
--   Then
--   $$
--   d\bigl([u_0,\dots,u_\ell],[c_0,\dots,c_\ell]\bigr)\le\frac{a}{a-\ell}\,e .
--   $$
--   For $\ell=1$ this is due to Goyal and Guruswami [GG26]. It converts closeness at many points of the curve into interleaved closeness of the coefficient words.
--
--   **Formalization Note** The distinct parameters are an injective map `Fin a → F_q`; the bound is real.
--
--   Differences from the source:
--   - encoding: pairwise distinct z_1, …, z_a ∈ F_q → an injective z : Fin a → F_q; reason: same data
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.8, p.21

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_curve
import Definitions.Def_AGProxGap_interDist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Lemma 3.8** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.21; [GG26] for ℓ = 1): "Let a ≥ ℓ + 1 and c_0, . . . , c_ℓ ∈ F_q^n.
Suppose there exist pairwise distinct elements z_1, . . . , z_a ∈ F_q such that
d(r(z_h), Σ_{j=0}^ℓ c_j z_h^j) ≤ e for every h ∈ [a]. Then
d([u_0, . . . , u_ℓ], [c_0, . . . , c_ℓ]) ≤ a/(a−ℓ) e."

**Formalization Note** `F_q` is a finite field, `ℓ ≥ 1` is the §3 standing degree bound, and
`u_0, …, u_ℓ` are the words of the curve `r`. The pairwise distinct `z_1, …, z_a` are an injective
`z : Fin a → F_q`; `Σ_j c_j z_h^j` is `curve c (z h)`. The bound `a/(a − ℓ) · e` is real
(`a − ℓ ≥ 1`). -/
theorem lemma_3_8 {Fq : Type u} [Field Fq] [Fintype Fq] {n ℓ : ℕ} (hℓ : 1 ≤ ℓ) (e a : ℕ)
    (ha : ℓ + 1 ≤ a) (u c : Fin (ℓ + 1) → Fin n → Fq) (z : Fin a → Fq)
    (hz : Function.Injective z) (hclose : ∀ h, hammingDist (curve u (z h)) (curve c (z h)) ≤ e) :
    (interDist u c : ℝ) ≤ (a : ℝ) / ((a : ℝ) - ℓ) * e := by sorry

end AGProxGap
