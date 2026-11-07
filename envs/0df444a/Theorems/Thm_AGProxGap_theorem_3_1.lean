-- Prove2me | Theorems.Thm_AGProxGap_theorem_3_1
-- name    : AGProxGap.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:35.938206+00:00
-- url     : https://prove2.me/theorems/5c235aeb-6ebb-479d-9916-b815ab7deeb4
-- title:
--   Theorem 3.1 — CA for one-point AG codes below $d/2$ with threshold $\max\{\lfloor(\ell+1)n(D_Z-1)/(e+1)\rfloor+1,a\}$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix $\ell\ge1$. Let $e$ be an integer with $0\le e<d/2$ and $D_Z\ge 1$ an integer with $(d-2e)D_Z>\ell e$. For $u_0,\dots,u_\ell\in\mathbb F_q^n$ let $S=\{z\in\mathbb F_q: d(r(z),C)\le e\}$. If there is an integer $a\ge\ell+1$ with
--   $$
--   |S|\ge\max\Bigl\{\Bigl\lfloor\frac{(\ell+1)n(D_Z-1)}{e+1}\Bigr\rfloor+1,\ a\Bigr\},
--   $$
--   then there exist $v_0,\dots,v_\ell\in L(G)$ with
--   $$
--   d\bigl([u_0,\dots,u_\ell],[v_0(D),\dots,v_\ell(D)]\bigr)\le\frac{a}{a-\ell}\,e ,
--   $$
--   and in particular $d([u_0,\dots,u_\ell],C^{\ell+1})\le\frac{a}{a-\ell}e$.
--
--   This is the paper's main technical theorem for the half-distance regime; both soundness bounds of Theorem 1.1 are obtained from it by choosing $D_Z$ and $a$.
--
--   **Formalization Note** Both conclusions are stated; the second as the existence of codewords $c_0,\dots,c_\ell\in C$.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Theorem 3.1, p.17

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_divG
import Definitions.Def_AGProxGap_agCode
import Definitions.Def_AGProxGap_closeSet
import Definitions.Def_BeatingGV42_goppaCode
import Definitions.Def_AGProxGap_interDist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Theorem 3.1** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.17): "Let e be an integer with 0 ≤ e < d/2. Choose an integer
D_Z ≥ 1 such that (d − 2e)D_Z > ℓe. For u_0, . . . , u_ℓ ∈ F_q^n, let S = {z ∈ F_q : d(r(z), C) ≤ e}.
If there is an integer a ≥ ℓ + 1 such that |S| ≥ max{⌊(ℓ+1)n(D_Z−1)/(e+1)⌋ + 1, a}, then there
exist v_0, . . . , v_ℓ ∈ L(G) such that d([u_0, . . . , u_ℓ], [v_0(D), . . . , v_ℓ(D)]) ≤ a/(a−ℓ) e.
In particular, d([u_0, . . . , u_ℓ], C^{ℓ+1}) ≤ a/(a−ℓ) e."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. `ℓ ≥ 1` is the §3 standing degree bound (p.17), `d = n − m`,
`C = agCode P Pinf m`, `S = closeSet C u e`. The floor is natural-number division; the bound
`a/(a − ℓ) · e` is real. Both conclusions are stated; `d([u], C^{ℓ+1}) ≤ …` is the existence of
codewords `c_0, …, c_ℓ ∈ C` at interleaved distance at most the bound. -/
theorem theorem_3_1 {Fq : Type u} [Field Fq] [Fintype Fq] {F : Type v} [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hF : ConstantsAreBase Fq F)
    {n m : ℕ} {P : Fin n → Place Fq F} {Pinf : Place Fq F} (hP : OnePointData P Pinf m)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {e : ℕ} (he : 2 * e < n - m)
    (DZ : ℕ) (hDZ : 1 ≤ DZ) (hDZe : ℓ * e < (n - m - 2 * e) * DZ)
    (u : Fin (ℓ + 1) → Fin n → Fq) (a : ℕ) (ha : ℓ + 1 ≤ a)
    (hS : max ((ℓ + 1) * n * (DZ - 1) / (e + 1) + 1) a ≤ (closeSet (agCode P Pinf m) u e).card) :
    (∃ v : Fin (ℓ + 1) → F, (∀ j, v j ∈ LSpace (divG Pinf m)) ∧
      (interDist u (fun j => BeatingGV42.evalVec P (v j)) : ℝ) ≤ (a : ℝ) / ((a : ℝ) - ℓ) * e) ∧
    ∃ c : Fin (ℓ + 1) → Fin n → Fq, (∀ j, c j ∈ agCode P Pinf m) ∧
      (interDist u c : ℝ) ≤ (a : ℝ) / ((a : ℝ) - ℓ) * e := by sorry

end AGProxGap
