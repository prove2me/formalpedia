-- Prove2me | Theorems.Thm_AGProxGap_Supplement_theorem_5_7
-- name    : AGProxGap.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:23:25.585477+00:00
-- url     : https://prove2.me/theorems/615f2c12-cf44-4104-a5d4-e515bceb240d
-- title:
--   Theorem 5.7 — subspace-polynomial counterexample over $\mathbb F_{Q^6}$: $d(C)=n-m$ and CA needs $\sigma=1$
-- statement:
--   Let $Q$ be a prime power and $q=Q^6$. At a fixed level of the Garcia–Stichtenoth tower over $\mathbb F_q$ (with $s=Q^3$), with $n$ evaluation points and $b=[F_j:F_0]$, let
--   $$m=(q-2Q^2+1)b,\qquad e=n-(q-Q^2)b,$$
--   and $C=C_L(D,mP_\infty)$. Then:
--   1. $C$ has minimum distance $d(C)=n-m$;
--   2. there exist words $u_0,u_1\in\mathbb F_q^n$ such that $d(u_0+zu_1,C)=e$ for every $z\in\mathbb F_q$, but
--   $$d([u_0,u_1],C^2)\ge d(u_1,C)\ge e+(Q^2-Q)b;$$
--   3. consequently, for every $0\le\varepsilon<(Q^2-Q)b/e$, $(1,e,\sigma,\varepsilon)$-CA requires $\sigma=1$.
--
--   Over a fixed field, the radius $e$ exceeds half the minimum distance by a relative amount tending to zero along the tower, and correlated agreement fails with the largest possible soundness error.
--
--   **Formalization Note** "Requires $\sigma=1$" is: every real $\sigma$ for which $C$ has the CA property satisfies $\sigma\ge1$ (soundness parameters are at most $1$). The level is arbitrary.
--
--   Differences from the source:
--   - encoding: the Garcia–Stichtenoth tower over F_q (x_0 an indeterminate, roots y_{j+1} of y^s + y = x_j^{s+1}) → every GSTower datum in every ambient field Ω ⊇ F_q; reason: Y^s + Y − x_j^{s+1} is irreducible over F_j, so every datum is the tower up to isomorphism
--   - encoding: P_∞ the unique pole of x_0, D the sum of all other rational points, n = deg D, b = [F_j : F_0] → IsGSLevel (pole of x_0, injective enumeration of the other rational places), n the number of points, b = relfinrank F_0 F_j; reason: the unique pole is the only place with ord(x_0) < 0; every enumeration gives the same code up to coordinate order
--   - encoding: '(1, e, σ, ε)-CA requires σ ≥ X' → for every real σ, HasCA C 1 e σ ε → X ≤ σ; reason: the meaning of 'requires'
--   - encoding: d(·, C) and d([u_0, u_1], C²) ≥ X; d(C) → codeDist (infimum of Hamming distances); X ≤ interDist to every pair of codewords; minDist (infimum over distinct pairs); reason: the codes are nonempty with at least two codewords, so the infima are the minima
--   - encoding: m = (q − 2Q² + 1)b, e = n − (q − Q²)b with q = Q⁶ → (Q^6 − 2Q^2 + 1)b and n − (Q^6 − Q^2)b in ℕ; reason: exact; Q^6 ≥ 2Q^2 and n ≥ (q−1)b, so no subtraction truncates
--   - encoding: 'requires σ = 1' → for every real σ, HasCA C 1 e σ ε → 1 ≤ σ; reason: soundness parameters satisfy σ ≤ 1 (§2.2), so σ ≥ 1 is σ = 1
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §5.3, Theorem 5.7, p.39; §2.4, p.15; §5, pp.34–35

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AGProxGap_agCode
import Definitions.Def_AGProxGap_curve
import Definitions.Def_AGProxGap_interDist
import Definitions.Def_AGProxGap_HasCA
import Definitions.Def_AGProxGap_Supplement_codeDist
import Definitions.Def_AGProxGap_Supplement_minDist
import Definitions.Def_AGProxGap_Supplement_GSTower
import Definitions.Def_AGProxGap_Supplement_IsGSLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

universe u v

namespace AGProxGap.Supplement

/-- **Theorem 5.7** (subspace-polynomial counterexample over a fixed field; (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §5.3, p.39):
"Let Q be a prime power and set q = Q^6. At a fixed level of the Garcia-Stichtenoth tower in
Section 2.4, let m = (q − 2Q^2 + 1)b and e = n − (q − Q^2)b. The code C = C_L(D, mP_∞) has
minimum distance d(C) = n − m. Moreover, there exist words u_0, u_1 ∈ F_q^n such that
d(u_0 + zu_1, C) = e for every z ∈ F_q, but d([u_0, u_1], C^2) ≥ d(u_1, C) ≥ e + (Q^2 − Q)b.
Consequently, for every 0 ≤ ε < (Q^2 − Q)b/e, (1, e, σ, ε)-CA requires σ = 1."

**Formalization Note** `F_q` is any finite field with `Q^6` elements, `Q` a prime power; the tower
is any `GSTower` datum over it with `s = Q^3` (so `q = s²`) in any ambient field `Ω`, at an
arbitrary level `j`, with evaluation data `IsGSLevel`, `n` points and `b = [F_j : F_0]`.
`m = (Q^6 − 2Q^2 + 1)b` and `e = n − (Q^6 − Q^2)b` are natural numbers (no truncation:
`Q^6 ≥ 2Q^2` and `n ≥ (q−1)b`). `d(·, C)` is `codeDist`, `d(C)` the actual minimum distance
`minDist`; `d([u_0, u_1], C²) ≥ d(u_1, C)` is "`d(u_1, C) ≤` the interleaved distance to every pair
of codewords". The line is `u_0 + z u_1` (the base `curve` with `ℓ = 1`). "CA requires `σ = 1`" is:
every real `σ` for which `C` has `(1, e, σ, ε)`-CA satisfies `1 ≤ σ` (the soundness range of
§2.2 is `σ ≤ 1`). -/
theorem theorem_5_7 (Q : ℕ) (hQ : IsPrimePow Q)
    (Fq : Type u) [Field Fq] [Fintype Fq] (hq : Fintype.card Fq = Q ^ 6)
    (Ω : Type v) [Field Ω] [Algebra Fq Ω] (T : GSTower Fq Ω (Q ^ 3)) (j : ℕ)
    (n : ℕ) (P : Fin n → Place Fq (T.field j)) (Pinf : Place Fq (T.field j))
    (hlev : IsGSLevel T j P Pinf) :
    let b : ℕ := T.b j
    let m : ℕ := (Q ^ 6 - 2 * Q ^ 2 + 1) * b
    let e : ℕ := n - (Q ^ 6 - Q ^ 2) * b
    let C : Set (Fin n → Fq) := AGProxGap.agCode P Pinf m
    minDist C = n - m ∧
    (∃ u0 u1 : Fin n → Fq,
      (∀ z : Fq, codeDist C (AGProxGap.curve ![u0, u1] z) = e) ∧
      (∀ c : Fin 2 → Fin n → Fq, (∀ k, c k ∈ C) → codeDist C u1 ≤ AGProxGap.interDist ![u0, u1] c) ∧
      e + (Q ^ 2 - Q) * b ≤ codeDist C u1) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < (((Q : ℝ) ^ 2 - Q) * b) / e → ∀ σ : ℝ, AGProxGap.HasCA C 1 e σ ε →
      1 ≤ σ) := by sorry

end AGProxGap.Supplement
