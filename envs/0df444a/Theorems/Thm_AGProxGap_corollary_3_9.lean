-- Prove2me | Theorems.Thm_AGProxGap_corollary_3_9
-- name    : AGProxGap.corollary_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:22.353117+00:00
-- url     : https://prove2.me/theorems/61562039-b40f-4ce2-a3c6-ce751632eec0
-- title:
--   Corollary 3.9 — CA and PG with slack $\varepsilon$ at $\sigma_\varepsilon=\max\{M_e,\ell+\lceil\ell/\varepsilon\rceil-1\}/q$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix $\ell\ge1$, an integer $e$ with $0\le e<d/2$ and $0<\varepsilon<1$, and set
--   $$
--   D_Z=\Bigl\lfloor\frac{\ell e}{d-2e}\Bigr\rfloor+1,\qquad M_e=\Bigl\lfloor\frac{(\ell+1)n(D_Z-1)}{e+1}\Bigr\rfloor,\qquad \delta=\frac dn,\ \gamma=\frac en .
--   $$
--   Then:
--   1. $M_e<\ell(\ell+1)/(\delta-2\gamma)$;
--   2. for all $u_0,\dots,u_\ell$, if $|S|\ge\max\{M_e+1,\ \ell+\lceil\ell/\varepsilon\rceil\}$, there exist $v_0,\dots,v_\ell\in L(G)$ with $d([u_0,\dots,u_\ell],[v_0(D),\dots,v_\ell(D)])\le(1+\varepsilon)e$;
--   3. $C$ has $(\ell,e,\sigma_\varepsilon,\varepsilon)$-CA and $(\ell,e,\sigma_\varepsilon,\varepsilon)$-PG, where
--   $$
--   \sigma_\varepsilon=\frac{\max\{M_e,\ \ell+\lceil\ell/\varepsilon\rceil-1\}}{q};
--   $$
--   4. $\sigma_\varepsilon=O\bigl(\max\{\ell(\ell+1)/(\delta-2\gamma),\ \ell/\varepsilon\}/q\bigr)$: there is one absolute constant $K_0$ with $\sigma_\varepsilon\le K_0\max\{\ell(\ell+1)/(\delta-2\gamma),\ell/\varepsilon\}/q$ for all parameters.
--
--   For fixed $\ell,\delta,\gamma,\varepsilon$ with $\delta>2\gamma$ the bound does not depend on $n$; this gives clause (A) of Theorem 1.1.
--
--   **Formalization Note** $D_Z$, $M_e$ are the definitions `DZ`, `Me` (floors as natural-number division). Item 4 is stated for all integers $q\ge1$, $0<m<n$, $\ell\ge1$, $2e<n-m$ and reals $0<\varepsilon<1$, since $\sigma_\varepsilon$ depends on the code only through these numbers, with $K_0$ chosen before all of them.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
--   - reading: σ = O(…) → ∃ one constant chosen before every other quantity (field, curve, code, ℓ, e, ε); reason: strongest reading of the O(·); the proof gives the constant 2
--   - generalization: the O(·) bound on σ_ε for the code C → the bound for all integers q ≥ 1, 0 < m < n, ℓ ≥ 1, 2e < n − m and reals 0 < ε < 1; reason: σ_ε depends on C only through q, n, m, ℓ, e, ε, so the arithmetic statement specializes to every code
--   - reading: “For fixed ℓ, δ, γ, ε with δ > 2γ, this bound is independent of n” → no separate conjunct; it is carried by the second conjunct, whose bound K₀ · max{ℓ(ℓ+1)/(δ − 2γ), ℓ/ε}/q depends on n only through δ = d/n and γ = e/n; reason: the sentence is a remark on the O(·) bound, not a further claim
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Corollary 3.9, p.22

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
import Definitions.Def_AGProxGap_HasCA
import Definitions.Def_AGProxGap_HasPG
import Definitions.Def_AGProxGap_Me

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Corollary 3.9** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.22): "Let e be an integer with 0 ≤ e < d/2, let 0 < ε < 1, and
set D_Z := ⌊ℓe/(d − 2e)⌋ + 1, M_e := ⌊(ℓ + 1)n(D_Z − 1)/(e + 1)⌋. (3) Writing δ = d/n and γ = e/n,
we have M_e < ℓ(ℓ + 1)/(δ − 2γ). If |S| ≥ max{M_e + 1, ℓ + ⌈ℓ/ε⌉}, then there exist
v_0, . . . , v_ℓ ∈ L(G) such that d([u_0, . . . , u_ℓ], [v_0(D), . . . , v_ℓ(D)]) ≤ (1 + ε)e.
Consequently, C has (ℓ, e, σ_ε, ε)-CA and (ℓ, e, σ_ε, ε)-PG where σ_ε := max{M_e, ℓ+⌈ℓ/ε⌉−1}/q =
O(max{ℓ(ℓ+1)/(δ−2γ), ℓ/ε}/q). For fixed ℓ, δ, γ, ε with δ > 2γ, this bound is independent of n."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. `ℓ ≥ 1` (§3, p.17), `d = n − m`, `D_Z = DZ ℓ e d` and
`M_e = Me ℓ e n d` (floors as natural-number division), `δ = d/n`, `γ = e/n` and `q = |F_q|` real,
`⌈ℓ/ε⌉` is `Nat.ceil`. The first conjunct holds for every one-point code and collects the first
three assertions: the bound on `M_e`, the agreement under the threshold on `|S|`, and CA and PG at
`σ_ε`. The second conjunct is the `O(·)`: one constant `K₀`, chosen before every parameter,
with `σ_ε ≤ K₀ · max{ℓ(ℓ+1)/(δ − 2γ), ℓ/ε}/q`. It is stated for all integers `q ≥ 1`,
`0 < m < n`, `ℓ ≥ 1`, `2e < n − m` and reals `0 < ε < 1`, since `σ_ε` depends on the code only
through these numbers. The sentence "For fixed ℓ, δ, γ, ε … independent of n" is a reading of
this bound, not a further claim. -/
theorem corollary_3_9 :
    (∀ (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
      [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F], ConstantsAreBase Fq F →
      ∀ (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F), OnePointData P Pinf m →
      ∀ ℓ e : ℕ, 1 ≤ ℓ → 2 * e < n - m → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ((Me ℓ e n (n - m) : ℝ) <
            (ℓ : ℝ) * (ℓ + 1) / (((n : ℝ) - m) / n - 2 * ((e : ℝ) / n))) ∧
        (∀ u : Fin (ℓ + 1) → Fin n → Fq,
          max (Me ℓ e n (n - m) + 1) (ℓ + ⌈(ℓ : ℝ) / ε⌉₊) ≤ (closeSet (agCode P Pinf m) u e).card →
            ∃ v : Fin (ℓ + 1) → F, (∀ j, v j ∈ LSpace (divG Pinf m)) ∧
              (interDist u (fun j => BeatingGV42.evalVec P (v j)) : ℝ) ≤ (1 + ε) * e) ∧
        HasCA (agCode P Pinf m) ℓ e (((max (Me ℓ e n (n - m)) (ℓ + ⌈(ℓ : ℝ) / ε⌉₊ - 1) : ℕ) : ℝ) / (Fintype.card Fq : ℝ)) ε ∧
        HasPG (agCode P Pinf m) ℓ e (((max (Me ℓ e n (n - m)) (ℓ + ⌈(ℓ : ℝ) / ε⌉₊ - 1) : ℕ) : ℝ) / (Fintype.card Fq : ℝ)) ε) ∧
    ∃ K₀ : ℝ, ∀ q n m ℓ e : ℕ, 1 ≤ q → 0 < m → m < n → 1 ≤ ℓ → 2 * e < n - m →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ((max (Me ℓ e n (n - m)) (ℓ + ⌈(ℓ : ℝ) / ε⌉₊ - 1) : ℕ) : ℝ) / q ≤
          K₀ * max ((ℓ : ℝ) * (ℓ + 1) / (((n : ℝ) - m) / n - 2 * ((e : ℝ) / n))) ((ℓ : ℝ) / ε) /
            q := by sorry

end AGProxGap
