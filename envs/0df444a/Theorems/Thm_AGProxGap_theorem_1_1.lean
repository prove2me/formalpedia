-- Prove2me | Theorems.Thm_AGProxGap_theorem_1_1
-- name    : AGProxGap.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:40:37.868502+00:00
-- url     : https://prove2.me/theorems/9ef0e02b-c89d-455f-9a75-16f6a212acfd
-- title:
--   Theorem 1.1 — CA up to half the designed distance for one-point AG codes, with and without slack
-- statement:
--   Let $X/\mathbb F_q$ be a smooth, projective, geometrically irreducible curve of genus $\mathfrak g$, let $P_1,\dots,P_n,P_\infty\in X(\mathbb F_q)$ be pairwise distinct rational points, $D=P_1+\dots+P_n$, $G=mP_\infty$ with $0<m<n$, $C=C_L(D,G)$ the one-point AG code, and $d=n-m$ its designed distance. Fix an integer $\ell\ge1$ (the degree of the curves $r(Z)=\sum_{j=0}^{\ell}u_jZ^j$), and let $e\ge 1$ be an integer with $e<(n-m)/2$.
--
--   (A) For every $0<\varepsilon<1$, $C$ has $(\ell,e,\sigma_\varepsilon,\varepsilon)$-correlated agreement with
--   $$
--   \sigma_\varepsilon=O\Bigl(\max\Bigl\{\frac{\ell}{\varepsilon q},\ \frac{\ell(\ell+1)n}{(n-m-2e)q}\Bigr\}\Bigr),
--   $$
--   the constant in $O(\cdot)$ being absolute.
--
--   (B) $C$ has $(\ell,e,\sigma_0,0)$-correlated agreement with
--   $$
--   \sigma_0=\min\Bigl\{1,\ \max\Bigl\{\frac{\ell(e+1)}{q},\ \frac{\ell(\ell+1)n}{(n-m-2e)q}\Bigr\}\Bigr\}.
--   $$
--
--   The radius reaches half the designed distance $d=n-m$ with no loss depending on the genus, and for fixed $\ell$, $\varepsilon$ and relative parameters the soundness error does not grow with the length $n$, which for AG codes may exceed $q$.
--
--   **Formalization Note** The constant of (A) is one real number chosen before the field, the curve, the code, $\ell$, $e$ and $\varepsilon$. All soundness formulas are real numbers, with $q=|\mathbb F_q|$.
--
--   Differences from the source:
--   - encoding: a smooth projective geometrically irreducible curve X/F_q of genus 𝔤, points of X(F_q) → a field F with IsCurveOver F_q F, Algebra.EssFiniteType F_q F, ConstantsAreBase F_q F; rational places (IsRational); genus genusFF F_q F; reason: over a finite (perfect) field these are exactly the function fields of such curves, and rational places are the rational points
--   - generalization: an [n, m + 1 − 𝔤, ≥ n − m] one-point AG code with 2𝔤 − 1 ≤ m < n (§1.1, p.3) → every one-point AG code with 0 < m < n; reason: the proof (§3) never uses 2𝔤 − 1 ≤ m or l(G) = m + 1 − 𝔤; the paper's codes satisfy 0 < m < n
--   - reading: σ = O(…) → ∃ one constant chosen before every other quantity (field, curve, code, ℓ, e, ε); reason: strongest reading of the O(·); the proof gives the constant 2
--   - encoding: C = {f(D) : f ∈ L(G)} → agCode P Pinf m, the F_q-span of that image (BeatingGV42.goppaCode); reason: under OnePointData the image is already a subspace, so the span is the same set
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Theorem 1.1, p.4; ℓ fixed on p.4

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AGProxGap_OnePointData
import Definitions.Def_AGProxGap_agCode
import Definitions.Def_AGProxGap_HasCA

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Theorem 1.1** (CA up to half the designed distance; Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §1.1, p.4): "Let C be an
[n, m + 1 − 𝔤, ≥ n − m] one-point AG code. Let e ≥ 1 be an integer and assume e < (n−m)/2. For
every 0 < ε < 1, C has (ℓ, e, σ_ε, ε)-CA with σ_ε = O(max{ℓ/(εq), ℓ(ℓ+1)n/((n−m−2e)q)}). It also
has (ℓ, e, σ_0, 0)-CA with σ_0 = min{1, max{ℓ(e+1)/q, ℓ(ℓ+1)n/((n−m−2e)q)}}." The degree bound is
fixed on p.4: "Fix an integer ℓ ≥ 1."

**Formalization Note** The function field `F/F_q` of the smooth projective geometrically irreducible curve `X` is a field
with `IsCurveOver F_q F`, `Algebra.EssFiniteType F_q F` and `ConstantsAreBase F_q F` (full
constant field `F_q`); the points `P_1, …, P_n, P_∞ ∈ X(F_q)` are rational places, pairwise
distinct, and `0 < m < n` (`OnePointData`). The §3 assumption `l(G) = m + 1 − 𝔤` (p.17) and the
§1.1 condition `2𝔤 − 1 ≤ m` (p.3) are dropped: the statement holds without them. `C = agCode P Pinf m`, `q = |F_q|`, and all soundness formulas
are real. Clause (A) reads `O(·)` as one absolute constant `C₀`, chosen before the field, the
curve, the code, `ℓ`, `e` and `ε`; clause (B) is the slack-free statement. Both are for every
`ℓ ≥ 1` and every integer `e ≥ 1` with `2e < n − m`. -/
theorem theorem_1_1 :
    (∃ C₀ : ℝ, ∀ (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
      [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F], ConstantsAreBase Fq F →
      ∀ (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F), OnePointData P Pinf m →
      ∀ ℓ e : ℕ, 1 ≤ ℓ → 1 ≤ e → 2 * e < n - m → ∀ ε : ℝ, 0 < ε → ε < 1 →
        HasCA (agCode P Pinf m) ℓ e
          (C₀ * max ((ℓ : ℝ) / (ε * Fintype.card Fq)) ((ℓ : ℝ) * (ℓ + 1) * n / (((n : ℝ) - m - 2 * e) * Fintype.card Fq))) ε) ∧
    (∀ (Fq : Type u) [Field Fq] [Fintype Fq] (F : Type v) [Field F] [Algebra Fq F]
      [IsCurveOver Fq F] [Algebra.EssFiniteType Fq F], ConstantsAreBase Fq F →
      ∀ (n m : ℕ) (P : Fin n → Place Fq F) (Pinf : Place Fq F), OnePointData P Pinf m →
      ∀ ℓ e : ℕ, 1 ≤ ℓ → 1 ≤ e → 2 * e < n - m →
        HasCA (agCode P Pinf m) ℓ e
          (min 1 (max ((ℓ : ℝ) * (e + 1) / Fintype.card Fq) ((ℓ : ℝ) * (ℓ + 1) * n / (((n : ℝ) - m - 2 * e) * Fintype.card Fq)))) 0) := by sorry

end AGProxGap
