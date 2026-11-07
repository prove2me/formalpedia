-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_4
-- name    : AGProxGap.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:59.022315+00:00
-- url     : https://prove2.me/theorems/1a5e3df2-4831-463e-a7de-035ae427384a
-- title:
--   Lemma 3.4 — Berlekamp–Welch interpolation: $A(P_i,Z)r_i(Z)=B(P_i,Z)$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix an integer $\ell\ge 1$, words $u_0,\dots,u_\ell\in\mathbb F_q^n$ with $r(z)=\sum_ju_jz^j$ and $r_i(Z)=\sum_ju_{j,i}Z^j$, an integer $e$ with $0\le e<d/2$, and an integer $D_Z\ge 1$ with $(d-2e)D_Z>\ell e$. Let $K/\mathbb F_q$ be a finite extension, with the points $P_i,P_\infty$ on $X_K$, and let $H$ be an effective divisor on $X_K$ of degree $d-e+\mathfrak g-1$, with $\operatorname{supp}H\cap(\operatorname{supp}D\cup\operatorname{supp}G)=\emptyset$ and $L_K(G+H-\sum_{i\in I}P_i)=\{0\}$ for every $I\subseteq[n]$ with $|I|=n-e$ (as given by Lemma 3.3).
--
--   Then there exist a nonzero polynomial $A(\cdot,Z)\in L_K(H)[Z]$ with $\deg_ZA\le D_Z-1$ and a polynomial $B(\cdot,Z)\in L_K(G+H)[Z]$ with $\deg_ZB\le D_Z+\ell-1$ such that
--   $$
--   A(P_i,Z)\,r_i(Z)=B(P_i,Z)\qquad\text{for every } i\in[n].
--   $$
--   This is the interpolation step of the proof of Theorem 3.1, with coefficients that are functions on the curve instead of polynomials.
--
--   **Formalization Note** $A,B$ are polynomials over the function field $K(X)$ whose coefficients lie in the Riemann–Roch spaces; $A(P_i,Z)$ is `evalPolyAt`; $r_i$ is mapped from $\mathbb F_q[Z]$ to $K[Z]$.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - encoding: a finite extension K/F_q, the curve X_K and the points P_i, P_∞ on it → a ConstExt datum: finite K, FK = K·F a function field with constants K, unique places lift i, liftInf over P_i, P_∞; reason: over F_q with full constant field FK is the function field of X_K and these are its points over P_i, P_∞
--   - generalization: the divisor H (and K) given by Lemma 3.3 → any datum E and any divisor H with Lemma 3.3's conclusion (effective, degree d − e + 𝔤 − 1, H(P'_i) = H(P'_∞) = 0, HasVanishing); reason: the proof uses only these properties; the constructed H is one such divisor
--   - encoding: A(·, Z) ∈ L_K(H)[Z], deg_Z A, A(P_i, Z) → Polynomial FK with all coefficients in LSpace H, natDegree, evalPolyAt (E.lift i) A; reason: same objects
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.4, p.19

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Lemma 3.4** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.19): "Fix the finite extension K/F_q and the divisor H given by
Lemma 3.3. Let D_Z ≥ 1 be an integer satisfying (d − 2e)D_Z > ℓe. Then there exist a nonzero
polynomial A(·, Z) ∈ L_K(H)[Z] with deg_Z A ≤ D_Z − 1, and a polynomial B(·, Z) ∈ L_K(G + H)[Z]
with deg_Z B ≤ D_Z + ℓ − 1, such that, for every i ∈ [n], we have A(P_i, Z)r_i(Z) = B(P_i, Z)."

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
`r_i(Z) ∈ F_q[Z]` is `rpoly u i`, mapped to `K[Z]`. The words `u_0, …, u_ℓ` are
`u : Fin (ℓ + 1) → Fin n → F_q`. -/
theorem lemma_3_4 {Fq : Type u} [Field Fq] [Fintype Fq] {F : Type v} [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hF : ConstantsAreBase Fq F)
    {n m : ℕ} {P : Fin n → Place Fq F} {Pinf : Place Fq F} (hP : OnePointData P Pinf m)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {e : ℕ} (he : 2 * e < n - m)
    (E : ConstExt P Pinf) (H : Divisor E.K E.FK) (hH0 : 0 ≤ H)
    (hHdeg : Divisor.degree H = (n : ℤ) - m - e + genusFF Fq F - 1)
    (hHD : ∀ i, H (E.lift i) = 0) (hHG : H E.liftInf = 0) (hHvan : HasVanishing E m H e)
    (DZ : ℕ) (hDZ : 1 ≤ DZ) (hDZe : ℓ * e < (n - m - 2 * e) * DZ)
    (u : Fin (ℓ + 1) → Fin n → Fq) :
    ∃ A B : Polynomial E.FK, A ≠ 0 ∧ (∀ j, A.coeff j ∈ LSpace H) ∧ A.natDegree ≤ DZ - 1 ∧
      (∀ j, B.coeff j ∈ LSpace (divG E.liftInf m + H)) ∧ B.natDegree ≤ DZ + ℓ - 1 ∧
      ∀ i, evalPolyAt (E.lift i) A * (rpoly u i).map (algebraMap Fq E.K) =
        evalPolyAt (E.lift i) B := by sorry

end AGProxGap
