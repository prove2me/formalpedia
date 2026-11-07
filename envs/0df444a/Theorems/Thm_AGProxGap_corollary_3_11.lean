-- Prove2me | Theorems.Thm_AGProxGap_corollary_3_11
-- name    : AGProxGap.corollary_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:57.935528+00:00
-- url     : https://prove2.me/theorems/996e4d07-822d-49e7-b1de-00e0941e378c
-- title:
--   Corollary 3.11 — CA and PG without slack at $\sigma=\max\{M_e,\ell(e+1)\}/q$
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix $\ell\ge1$ and an integer $e$ with $0\le e<d/2$, and let $D_Z$, $M_e$ be as in (3). Then:
--   1. for all $u_0,\dots,u_\ell$, if $|S|\ge\max\{M_e+1,\ \ell(e+1)+1\}$, there exist $v_0,\dots,v_\ell\in L(G)$ with $d([u_0,\dots,u_\ell],[v_0(D),\dots,v_\ell(D)])\le e$;
--   2. $C$ has $(\ell,e,\sigma,0)$-CA and $(\ell,e,\sigma,0)$-PG, where
--   $$
--   \sigma=\frac{\max\{M_e,\ \ell(e+1)\}}{q};
--   $$
--   3. when $d=\delta n$ and $e=\gamma n$ with $\ell$ fixed and $\delta>2\gamma>0$, for all sufficiently large $n$ this bound becomes $\min\{1,\ell(e+1)/q\}$: there is $N_0$, depending only on $\ell,\delta,\gamma$, such that every such code with $n\ge N_0$ has $\max\{M_e,\ell(e+1)\}=\ell(e+1)$ and has $(\ell,e,\min\{1,\ell(e+1)/q\},0)$-CA and PG.
--
--   This gives clause (B) of Theorem 1.1.
--
--   **Formalization Note** Item 3 is the paper's last sentence read as above; the threshold $N_0$ is chosen before the curve and the code.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - generalization: §3 standing assumption l(G) = m + 1 − 𝔤 (§1.1: 2𝔤 − 1 ≤ m < n) → only 0 < m < n; reason: the proof never uses it (Riemann's inequality and d(C) ≥ n − m need only m < n and P_∞ ∉ supp D); the paper's codes satisfy 0 < m < n
--   - reading: “this bound becomes min{1, ℓ(e + 1)/q}” for sufficiently large n → ∃ N₀(ℓ, δ, γ): for n ≥ N₀, max{M_e, ℓ(e+1)} = ℓ(e+1) and CA and PG hold at min{1, ℓ(e+1)/q}; reason: the literal equality max{M_e, ℓ(e+1)}/q = min{1, ℓ(e+1)/q} fails when ℓ(e+1) > q; the proof shows M_e < ℓ(e+1) for large n, and CA/PG at σ ≥ 1 are vacuous
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Corollary 3.11, p.22

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

/-- **Corollary 3.11** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.22): "Let e be an integer with 0 ≤ e < d/2, and let D_Z and M_e
be as in (3). If |S| ≥ max{M_e + 1, ℓ(e + 1) + 1}, then there exist v_0, . . . , v_ℓ ∈ L(G) such
that d([u_0, . . . , u_ℓ], [v_0(D), . . . , v_ℓ(D)]) ≤ e. In particular, C has (ℓ, e, σ, 0)-CA and
(ℓ, e, σ, 0)-PG where σ := max{M_e, ℓ(e+1)}/q. When d = δn and e = γn with fixed ℓ and
δ > 2γ > 0 and sufficiently large n, this bound becomes min{1, ℓ(e + 1)/q}."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. `ℓ ≥ 1` (§3, p.17), `d = n − m`, `M_e = Me ℓ e n d`, `q = |F_q|`.
The first conjunct holds for every one-point code: agreement within `e` under the threshold, and
CA and PG at `σ`. The second conjunct reads the last sentence (the literal equality
`max{M_e, ℓ(e+1)}/q = min{1, ℓ(e+1)/q}` fails when `ℓ(e+1) > q`): for fixed `ℓ ≥ 1` and reals
`δ > 2γ > 0` there is `N₀` such that every one-point code with `n ≥ N₀`, `d = δn` and `e = γn` has
`max{M_e, ℓ(e+1)} = ℓ(e+1)`, and has CA and PG without slack at `min{1, ℓ(e+1)/q}`. `N₀` is chosen
before the curve and the code, so it depends on `ℓ, δ, γ` only. -/
theorem corollary_3_11 :
    (∀ (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
      [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F], ConstantsAreBase Fq F →
      ∀ (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F), OnePointData P Pinf m →
      ∀ ℓ e : ℕ, 1 ≤ ℓ → 2 * e < n - m →
        (∀ u : Fin (ℓ + 1) → Fin n → Fq,
          max (Me ℓ e n (n - m) + 1) (ℓ * (e + 1) + 1) ≤ (closeSet (agCode P Pinf m) u e).card →
            ∃ v : Fin (ℓ + 1) → F, (∀ j, v j ∈ LSpace (divG Pinf m)) ∧
              interDist u (fun j => BeatingGV42.evalVec P (v j)) ≤ e) ∧
        HasCA (agCode P Pinf m) ℓ e (((max (Me ℓ e n (n - m)) (ℓ * (e + 1)) : ℕ) : ℝ) / (Fintype.card Fq : ℝ)) 0 ∧
        HasPG (agCode P Pinf m) ℓ e (((max (Me ℓ e n (n - m)) (ℓ * (e + 1)) : ℕ) : ℝ) / (Fintype.card Fq : ℝ)) 0) ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ δ γ : ℝ, 0 < γ → 2 * γ < δ → ∃ N₀ : ℕ,
      ∀ (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
      [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F], ConstantsAreBase Fq F →
      ∀ (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F), OnePointData P Pinf m →
        ∀ e : ℕ, N₀ ≤ n → ((n : ℝ) - m = δ * n) → ((e : ℝ) = γ * n) →
          max (Me ℓ e n (n - m)) (ℓ * (e + 1)) = ℓ * (e + 1) ∧
          HasCA (agCode P Pinf m) ℓ e (min 1 ((ℓ : ℝ) * (e + 1) / (Fintype.card Fq : ℝ))) 0 ∧
          HasPG (agCode P Pinf m) ℓ e (min 1 ((ℓ : ℝ) * (e + 1) / (Fintype.card Fq : ℝ))) 0 := by sorry

end AGProxGap
