-- Prove2me | Theorems.Thm_AGProxGap_Supplement_theorem_4_1
-- name    : AGProxGap.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:21:09.83023+00:00
-- url     : https://prove2.me/theorems/f6170cb4-d39e-4b85-9fde-c70957502061
-- title:
--   Theorem 4.1 — MCA up to the Johnson radius: $|S|\le B_e$ and $(\ell,e,\min\{1,B_e/q\})$-MCA
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ pairwise distinct, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $1\le m<n$ and $m\ge2\mathfrak g-1$, and $C=C_L(D,G)$; let $\rho=m/n$ and fix $\ell\ge1$. Fix a real $0<\eta<1-\sqrt\rho$ and let $s,N,D_Y,D_Z$ and $B_e$ be
--   $$s=\Bigl\lceil\tfrac{2\sqrt\rho}{\eta}\Bigr\rceil+2,\quad N=\lceil(s+1)\sqrt{mn}\rceil+\mathfrak g-1,\quad D_Y=\Bigl\lfloor\tfrac{N-\mathfrak g}{m}\Bigr\rfloor,\quad D_Z=\ell sD_Y,$$
--   $$B_e=(2D_Y+1)D_Z+\frac{n-m}{n-m-e}\bigl(4mD_YD_Z+\ell D_Y\bigr)+\ell D_Y(e+1).$$
--   Let $e$ be an integer with $0\le e\le(1-\sqrt\rho-\eta)n$, fix $u_0,\dots,u_\ell\in\mathbb F_q^n$, and let $S\subseteq\mathbb F_q$ be the set of parameters $z$ for which there are $f\in L(G)$ and $A\subseteq[n]$ such that $(z,f,A)$ is an MCA-bad $e$ agreement witness. Then
--   $$|S|\le B_e,$$
--   and consequently $C$ has $(\ell,e,\sigma)$-MCA with $\sigma=\min\{1,B_e/q\}$.
--
--   This is mutual correlated agreement for one-point AG codes all the way to the Johnson radius $1-\sqrt\rho$, with a soundness error $O(\ell n/(\eta^3q))$ (Remark 4.11); it is the formal version of Theorem 1.4.
--
--   **Formalization Note** The curve is its function field $F/\mathbb F_q$ with full constant field and the points are rational places, as in the mission's published definitions; $m\ge2\mathfrak g-1$ is written $2\mathfrak g\le m+1$ in $\mathbb N$ with $\mathfrak g$ the platform's genus. All quantities in the radius condition and in $B_e$ are real.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: the base mission's convention; over a finite (perfect) field these are exactly the function fields of such curves
--   - encoding: §4's assumption m ≥ 2𝔤 − 1 → 2 * genusFF F_q F ≤ m + 1 in ℕ; reason: same condition without natural subtraction
--   - encoding: C = C_L(D, G) = {f(D) : f ∈ L(G)}; S defined through f ∈ L(G) → agCode P Pinf m (the base definition) and mcaBadSet with c ∈ agCode; reason: under OnePointData the code is exactly the evaluation image, so c ∈ C is c = f(D) with f ∈ L(G)
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §4, p.23 (standing assumptions, parameters, Theorem 4.1); Definition 2.4, p.14

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_agCode
import Definitions.Def_AGProxGap_Supplement_mcaBadSet
import Definitions.Def_AGProxGap_Supplement_HasMCA
import Definitions.Def_AGProxGap_Supplement_Be

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap.Supplement

/-- **Theorem 4.1** (MCA up to the Johnson radius; (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §4, p.23): "Here we assume m ≥ 1 and
m ≥ 2𝔤 − 1. Fix an integer ℓ ≥ 1. … Fix a real number 0 < η < 1 − √ρ and set
s := ⌈2√ρ/η⌉ + 2, N := ⌈(s + 1)√(mn)⌉ + 𝔤 − 1, D_Y := ⌊(N − 𝔤)/m⌋, D_Z := ℓsD_Y.
Theorem 4.1. Let e be an integer satisfying 0 ≤ e ≤ (1−√ρ−η)n, and fix u_0, . . . , u_ℓ ∈ F_q^n.
Let S ⊆ F_q be the set of parameters z for which there exist f ∈ L(G) and A ⊆ [n] such that
(z, f, A) is an MCA-bad e agreement witness. Then
|S| ≤ B_e := (2D_Y + 1)D_Z + (n − m)/(n − m − e) (4mD_Y D_Z + ℓD_Y) + ℓD_Y(e + 1).
Consequently, C has (ℓ, e, σ)-MCA with σ = min{1, B_e/q}."

**Formalization Note** The curve and code are as in the base mission: `F/F_q` with
`IsCurveOver`, `Algebra.EssFiniteType`, `ConstantsAreBase`; `OnePointData` (distinct rational
`P_1, …, P_n, P_∞`, `0 < m < n`); `C = agCode P Pinf m`. §4's standing assumption `m ≥ 2𝔤 − 1`
is kept as `2𝔤 ≤ m + 1` with `𝔤 = genusFF F_q F`. `ρ = m/n`, `q = |F_q|`, and all of `η`, `√ρ`,
`B_e` and the radius condition are real. `S` is `mcaBadSet` (every `A` with `|A| ≥ n − e`), and
`B_e` with its parameters `s, N, D_Y, D_Z` is `Be ℓ m n 𝔤 e η`. -/
theorem theorem_4_1 (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
    [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F] (hconst : ConstantsAreBase Fq F)
    (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F) (hD : AGProxGap.OnePointData P Pinf m)
    (hgenus : 2 * genusFF Fq F ≤ m + 1) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η < 1 - Real.sqrt ((m : ℝ) / n)) (e : ℕ)
    (he : (e : ℝ) ≤ (1 - Real.sqrt ((m : ℝ) / n) - η) * n) :
    (∀ u : Fin (ℓ + 1) → Fin n → Fq,
      ((mcaBadSet (AGProxGap.agCode P Pinf m) u e).card : ℝ) ≤ Be ℓ m n (genusFF Fq F) e η) ∧
    HasMCA (AGProxGap.agCode P Pinf m) ℓ e
      (min 1 (Be ℓ m n (genusFF Fq F) e η / (Fintype.card Fq : ℝ))) := by sorry

end AGProxGap.Supplement
