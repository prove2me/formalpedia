-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_3
-- name    : AGProxGap.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:55.374904+00:00
-- url     : https://prove2.me/theorems/9e5b891c-bc2c-4d52-8650-ba6bf269345f
-- title:
--   Lemma 3.3 — an auxiliary divisor $H$ of degree $d-e+\mathfrak g-1$ over a finite extension
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance.
--
--   Fix an integer $0\le e<d$ and set $h=d-e+\mathfrak g-1$. Then there are a finite extension $K/\mathbb F_q$ and an effective divisor $H$ on $X_K$ of degree $h$ such that
--   $$
--   \operatorname{supp}H\cap(\operatorname{supp}D\cup\operatorname{supp}G)=\emptyset
--   \quad\text{and}\quad
--   L_K\Bigl(G+H-\sum_{i\in I}P_i\Bigr)=\{0\}\ \text{ for every } I\subseteq[n],\ |I|=n-e .
--   $$
--   So a function of $L_K(G+H)$ vanishing at $n-e$ evaluation points is zero. This replaces the polynomial degree argument of the Reed–Solomon proof and is how the genus term is removed from the radius.
--
--   **Formalization Note** $K$, $X_K$ and the points on it are a `ConstExt` datum (finite $K$, $K(X)=K\cdot F$, unique places $P_i'$, $P_\infty'$ over $P_i$, $P_\infty$), which the statement asserts to exist. The support condition is $H(P_i')=H(P_\infty')=0$; the degree is over $K$; the genus is `genusFF` of $F/\mathbb F_q$.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - encoding: a finite extension K/F_q, the curve X_K and the points P_i, P_∞ on it → a ConstExt datum: finite K, FK = K·F a function field with constants K, unique places lift i, liftInf over P_i, P_∞; reason: over F_q with full constant field FK is the function field of X_K and these are its points over P_i, P_∞
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.3, p.18

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_ConstExt
import Definitions.Def_AGProxGap_HasVanishing
import Definitions.Def_AGProxGap_divG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Lemma 3.3** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.18): "Using the above definitions, fix an integer 0 ≤ e < d, and set
h := d−e+𝔤−1. Then there exist a finite extension K/F_q and an effective divisor H on X_K of
degree h such that supp(H) ∩ (supp(D) ∪ supp(G)) = ∅ and for every subset I ⊆ [n] with
|I| = n − e, L_K(G + H − Σ_{i∈I} P_i) = {0}."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. Here `d = n − m`, `𝔤 = genusFF F_q F`, and `h` is computed in
`ℤ`. "A finite extension `K/F_q` and the curve `X_K`" is a `ConstExt` datum `E` (the finite
extension `E.K`, the function field `E.FK = K · F_q(X)`, and the points `P'_i = E.lift i`,
`P'_∞ = E.liftInf` over `P_i`, `P_∞`). "Effective" is `0 ≤ H`, the degree is over `K`, and
`supp(H) ∩ (supp(D) ∪ supp(G)) = ∅` is `H(P'_i) = 0` for all `i` and `H(P'_∞) = 0`. The
vanishing property is `HasVanishing E m H e`, with `G = m P'_∞`. -/
theorem lemma_3_3 {Fq : Type u} [Field Fq] [Fintype Fq] {F : Type v} [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hF : ConstantsAreBase Fq F)
    {n m : ℕ} {P : Fin n → Place Fq F} {Pinf : Place Fq F} (hP : OnePointData P Pinf m)
    (e : ℕ) (he : e < n - m) :
    ∃ E : ConstExt P Pinf, ∃ H : Divisor E.K E.FK, 0 ≤ H ∧
      Divisor.degree H = (n : ℤ) - m - e + genusFF Fq F - 1 ∧
      (∀ i, H (E.lift i) = 0) ∧ H E.liftInf = 0 ∧ HasVanishing E m H e := by sorry

end AGProxGap
