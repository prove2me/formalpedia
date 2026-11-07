-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_5
-- name    : AGProxGap.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:03.104709+00:00
-- url     : https://prove2.me/theorems/d98ae36c-8986-41a6-9243-ed403e5bf108
-- title:
--   Lemma 3.5 — $B_z=A_zf_z$ for every $z\in S$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix an integer $\ell\ge 1$, words $u_0,\dots,u_\ell\in\mathbb F_q^n$ with $r(z)=\sum_ju_jz^j$ and $r_i(Z)=\sum_ju_{j,i}Z^j$, an integer $e$ with $0\le e<d/2$, and an integer $D_Z\ge 1$ with $(d-2e)D_Z>\ell e$. Let $K/\mathbb F_q$ be a finite extension, with the points $P_i,P_\infty$ on $X_K$, and let $H$ be an effective divisor on $X_K$ of degree $d-e+\mathfrak g-1$, with $\operatorname{supp}H\cap(\operatorname{supp}D\cup\operatorname{supp}G)=\emptyset$ and $L_K(G+H-\sum_{i\in I}P_i)=\{0\}$ for every $I\subseteq[n]$ with $|I|=n-e$ (as given by Lemma 3.3). Let $A(\cdot,Z)$, $B(\cdot,Z)$ be as in Lemma 3.4: $A\ne 0$ with coefficients in $L_K(H)$ and $\deg_ZA\le D_Z-1$, $B$ with coefficients in $L_K(G+H)$ and $\deg_ZB\le D_Z+\ell-1$, and $A(P_i,Z)r_i(Z)=B(P_i,Z)$ for all $i$. Let $S=\{z\in\mathbb F_q: d(r(z),C)\le e\}$ and, for $z\in S$, let $f_z\in L(G)$ be the unique function with $d(r(z),f_z(D))\le e$.
--
--   Then, regarding $f_z$ as an element of $L_K(G)$ and writing $A_z=A(\cdot,z)\in L_K(H)$, $B_z=B(\cdot,z)\in L_K(G+H)$,
--   $$
--   B_z=A_z\,f_z\qquad\text{for every } z\in S .
--   $$
--   So the interpolating pair recovers every decoded function $f_z$ as the quotient $B_z/A_z$ wherever $A_z\neq0$.
--
--   **Formalization Note** The statement is made for every $f\in L(G)$ within distance $e$ of $r(z)$ (only $f_z$ qualifies); $z\in\mathbb F_q$ is viewed in $K(X)$.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - encoding: a finite extension K/F_q, the curve X_K and the points P_i, P_∞ on it → a ConstExt datum: finite K, FK = K·F a function field with constants K, unique places lift i, liftInf over P_i, P_∞; reason: over F_q with full constant field FK is the function field of X_K and these are its points over P_i, P_∞
--   - generalization: the divisor H (and K) given by Lemma 3.3 → any datum E and any divisor H with Lemma 3.3's conclusion (effective, degree d − e + 𝔤 − 1, H(P'_i) = H(P'_∞) = 0, HasVanishing); reason: the proof uses only these properties; the constructed H is one such divisor
--   - encoding: A(·, Z) ∈ L_K(H)[Z], deg_Z A, A(P_i, Z) → Polynomial FK with all coefficients in LSpace H, natDegree, evalPolyAt (E.lift i) A; reason: same objects
--   - encoding: the unique f_z ∈ L(G) with d(r(z), f_z(D)) ≤ e → every f ∈ L(G) with hammingDist (curve u z) (BeatingGV42.evalVec P f) ≤ e; reason: such an f is unique since e < d/2, so the two statements are equivalent
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.5, p.20

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_ConstExt
import Definitions.Def_AGProxGap_HasVanishing
import Definitions.Def_AGProxGap_divG
import Definitions.Def_AGProxGap_rpoly
import Definitions.Def_AGProxGap_evalPolyAt
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

/-- **Lemma 3.5** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.20), with its preamble: "Fix the finite extension K/F_q and the
effective divisor H given by Lemma 3.3, and fix A(·, Z) and B(·, Z) as in Lemma 3.4. For every
z ∈ S, we regard f_z naturally as an element of L_K(G) and write A_z := A(·, z) ∈ L_K(H) and
B_z := B(·, z) ∈ L_K(G + H). Lemma 3.5. Using the above notation, for every z ∈ S, we have
B_z = A_z f_z."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. `K`, `X_K` and the points `P'_i`, `P'_∞` are a `ConstExt` datum `E`, and "the divisor H given by
Lemma 3.3" is any divisor `H` on `X_K` with Lemma 3.3's conclusion: effective, of degree
`d − e + 𝔤 − 1` (`𝔤 = genusFF F_q F`, `d = n − m`), `H(P'_i) = H(P'_∞) = 0`, and
`HasVanishing E m H e`. The section's standing data are kept: `ℓ ≥ 1` (§3, p.17), `2e < d` (the
`e` fixed in the proof of Theorem 3.1, `0 ≤ e < d/2`), and the integer `D_Z ≥ 1` with
`(d − 2e)D_Z > ℓe`. A polynomial `A(·, Z) ∈ L_K(H)[Z]` is a `Polynomial E.FK` whose coefficients all lie in
`LSpace H`; `deg_Z` is `natDegree`. `A(P_i, Z) ∈ K[Z]` is `evalPolyAt (E.lift i) A`, and
`r_i(Z) ∈ F_q[Z]` is `rpoly u i`, mapped to `K[Z]`. "A, B as in Lemma 3.4" are any
polynomials with Lemma 3.4's conclusion for the words `u`. `S = closeSet (agCode P Pinf m) u e`.
"The unique function `f_z ∈ L(G)` with `d(r(z), f_z(D)) ≤ e`" (p.17) is not chosen: the
statement is made for every `f ∈ L(G)` with `d(r(z), f(D)) ≤ e` (there is exactly one, as
`e < d/2`). `f_z` is regarded in `L_K(G)` through `algebraMap F E.FK`, and `A_z = A(·, z)` is
`A.eval z` with `z ∈ F_q ⊆ K(X)`. -/
theorem lemma_3_5 {Fq : Type u} [Field Fq] [Fintype Fq] {F : Type v} [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hF : ConstantsAreBase Fq F)
    {n m : ℕ} {P : Fin n → Place Fq F} {Pinf : Place Fq F} (hP : OnePointData P Pinf m)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {e : ℕ} (he : 2 * e < n - m)
    (E : ConstExt P Pinf) (H : Divisor E.K E.FK) (hH0 : 0 ≤ H)
    (hHdeg : Divisor.degree H = (n : ℤ) - m - e + genusFF Fq F - 1)
    (hHD : ∀ i, H (E.lift i) = 0) (hHG : H E.liftInf = 0) (hHvan : HasVanishing E m H e)
    (DZ : ℕ) (hDZ : 1 ≤ DZ) (hDZe : ℓ * e < (n - m - 2 * e) * DZ)
    (u : Fin (ℓ + 1) → Fin n → Fq)
    (A B : Polynomial E.FK) (hA0 : A ≠ 0) (hAL : ∀ j, A.coeff j ∈ LSpace H)
    (hAdeg : A.natDegree ≤ DZ - 1) (hBL : ∀ j, B.coeff j ∈ LSpace (divG E.liftInf m + H))
    (hBdeg : B.natDegree ≤ DZ + ℓ - 1)
    (hAB : ∀ i, evalPolyAt (E.lift i) A * (rpoly u i).map (algebraMap Fq E.K) =
      evalPolyAt (E.lift i) B) :
    ∀ z ∈ closeSet (agCode P Pinf m) u e, ∀ f ∈ LSpace (divG Pinf m),
      hammingDist (curve u z) (BeatingGV42.evalVec P f) ≤ e →
        B.eval (algebraMap Fq E.FK z) = A.eval (algebraMap Fq E.FK z) * algebraMap F E.FK f := by sorry

end AGProxGap
