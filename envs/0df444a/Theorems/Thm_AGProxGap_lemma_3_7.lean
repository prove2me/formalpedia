-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_7
-- name    : AGProxGap.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:38:28.327584+00:00
-- url     : https://prove2.me/theorems/b7233d6c-4d30-4813-8ce9-7d763001ac5b
-- title:
--   Lemma 3.7 — $f_z=\sum_{j=0}^{\ell}v_jz^j$ on $S$ with $v_j\in L(G)$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix an integer $\ell\ge 1$, words $u_0,\dots,u_\ell\in\mathbb F_q^n$ with $r(z)=\sum_ju_jz^j$ and $r_i(Z)=\sum_ju_{j,i}Z^j$, an integer $e$ with $0\le e<d/2$, and an integer $D_Z\ge 1$ with $(d-2e)D_Z>\ell e$. Let $S=\{z\in\mathbb F_q: d(r(z),C)\le e\}$ and, for $z\in S$, let $f_z\in L(G)$ be the unique function with $d(r(z),f_z(D))\le e$. If
--   $$
--   |S|\ge \ell+1\qquad\text{and}\qquad |S|>\frac{(\ell+1)n(D_Z-1)}{e+1},
--   $$
--   then there exist $v_0,\dots,v_\ell\in L(G)$ such that
--   $$
--   f_z=\sum_{j=0}^{\ell}v_jz^j\qquad\text{for every } z\in S .
--   $$
--   This is the step where the decoded functions are shown to lie on one polynomial curve in $L(G)$, as needed for correlated agreement.
--
--   **Formalization Note** The auxiliary $K$, $H$, $A$, $B$ fixed in the paper before this lemma occur only in its proof and are not part of the statement. The second hypothesis is a strict real inequality.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - encoding: the unique f_z ∈ L(G) with d(r(z), f_z(D)) ≤ e → every f ∈ L(G) with hammingDist (curve u z) (BeatingGV42.evalVec P f) ≤ e; reason: such an f is unique since e < d/2, so the two statements are equivalent
--   - encoding: stated after fixing K, H (Lemma 3.3) and A, B (Lemma 3.4) → no K, H, A, B in the statement; reason: they do not occur in the hypotheses or the conclusion, and they exist by Lemmas 3.3 and 3.4
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.7, p.20

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_divG
import Definitions.Def_AGProxGap_agCode
import Definitions.Def_AGProxGap_closeSet
import Definitions.Def_BeatingGV42_goppaCode

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Lemma 3.7** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.20): "If |S| ≥ ℓ+1 and |S| > (ℓ+1)n(D_Z−1)/(e+1), then there exist
v_0, . . . , v_ℓ ∈ L(G) such that f_z = Σ_{j=0}^ℓ v_j z^j for every z ∈ S."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. The standing data of the proof of Theorem 3.1 are kept: `ℓ ≥ 1`,
`2e < d` (`d = n − m`), the integer `D_Z ≥ 1` with `(d − 2e)D_Z > ℓe`, the words `u`, and
`S = closeSet (agCode P Pinf m) u e`. The auxiliary `K`, `H`, `A`, `B` of Lemmas 3.3–3.6 occur
only in the proof and are not part of the statement. The second hypothesis is the strict real
inequality (no floor). "The unique function `f_z ∈ L(G)` with `d(r(z), f_z(D)) ≤ e`" (p.17) is not chosen: the
statement is made for every `f ∈ L(G)` with `d(r(z), f(D)) ≤ e` (there is exactly one, as
`e < d/2`). -/
theorem lemma_3_7 {Fq : Type u} [Field Fq] [Fintype Fq] {F : Type v} [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hF : ConstantsAreBase Fq F)
    {n m : ℕ} {P : Fin n → Place Fq F} {Pinf : Place Fq F} (hP : OnePointData P Pinf m)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {e : ℕ} (he : 2 * e < n - m)
    (DZ : ℕ) (hDZ : 1 ≤ DZ) (hDZe : ℓ * e < (n - m - 2 * e) * DZ)
    (u : Fin (ℓ + 1) → Fin n → Fq)
    (hS : ℓ + 1 ≤ (closeSet (agCode P Pinf m) u e).card)
    (hS' : ((ℓ : ℝ) + 1) * n * ((DZ : ℝ) - 1) / ((e : ℝ) + 1) <
      ((closeSet (agCode P Pinf m) u e).card : ℝ)) :
    ∃ v : Fin (ℓ + 1) → F, (∀ j, v j ∈ LSpace (divG Pinf m)) ∧
      ∀ z ∈ closeSet (agCode P Pinf m) u e, ∀ f ∈ LSpace (divG Pinf m),
        hammingDist (curve u z) (BeatingGV42.evalVec P f) ≤ e →
          f = ∑ j : Fin (ℓ + 1), algebraMap Fq F z ^ (j : ℕ) * v j := by sorry

end AGProxGap
