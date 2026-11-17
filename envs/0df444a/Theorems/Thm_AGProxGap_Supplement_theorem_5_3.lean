-- Prove2me | Theorems.Thm_AGProxGap_Supplement_theorem_5_3
-- name    : AGProxGap.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:21:51.3432+00:00
-- url     : https://prove2.me/theorems/dace872b-5a06-4afd-a6e6-0bf4873a4a3b
-- title:
--   Theorem 5.3 — trace counterexample: $d(r(z),C)=e$ on $-(\mathbb F_q^*)^{p^a-1}$, CA needs $\sigma\ge\frac{q-1}{(p^a-1)q}$
-- statement:
--   Let $p$ be a prime, $a\ge1$ and $h\ge2$ integers, and $q=p^{2ah}$. At a fixed level of the Garcia–Stichtenoth tower over $\mathbb F_q$ (with $s=p^{ah}$), with $n$ evaluation points and $b=[F_j:F_0]$, let
--   $$m=\Bigl(1-\frac2{p^a}+\frac1{p^{3a}}\Bigr)qb,\qquad e=n-\Bigl(1-\frac1{p^a}\Bigr)qb,$$
--   $C=C_L(D,mP_\infty)$, $\rho=m/n$, and
--   $$u_0=x^{(1-2/p^a+1/p^{2a})q}(D),\qquad u_1=x^{(1-1/p^a)q}(D),\qquad r(z)=u_0+zu_1.$$
--   Then:
--   1. $d(r(z),C)=e$ for every $z\in-(\mathbb F_q^*)^{p^a-1}$;
--   2. $d([u_0,u_1],C^2)\ge(2-1/p^a)\,e$;
--   3. for every $0\le\varepsilon<1-1/p^a$, $(1,e,\sigma,\varepsilon)$-CA requires $\sigma\ge\dfrac{q-1}{(p^a-1)q}$;
--   4. $0<\dfrac en-\dfrac{d(C)}{2n}\le\dfrac1{2p^{3a}}$ and $e<(1-\sqrt\rho)\,n$.
--
--   Correlated agreement therefore fails, with soundness error bounded below independently of $q$ and $n$, at radii just above half the actual minimum distance and below the Johnson radius. This is the formal version of Theorem 1.6.
--
--   **Formalization Note** With $P'=p^a$ the integers are written exactly: $m=b(P'^{2h}-2P'^{2h-1}+P'^{2h-3})$, $e=n-b(P'^{2h}-P'^{2h-1})$, and the exponents of $u_0,u_1$ are $P'^{2h}-2P'^{2h-1}+P'^{2h-2}$ and $P'^{2h}-P'^{2h-1}$; none of the natural subtractions truncates. $-(\mathbb F_q^*)^{p^a-1}=\{-w^{p^a-1}:w\neq0\}$; $d(C)$ is the actual minimum distance. The level is arbitrary.
--
--   Differences from the source:
--   - encoding: the Garcia–Stichtenoth tower over F_q (x_0 an indeterminate, roots y_{j+1} of y^s + y = x_j^{s+1}) → every GSTower datum in every ambient field Ω ⊇ F_q; reason: Y^s + Y − x_j^{s+1} is irreducible over F_j, so every datum is the tower up to isomorphism
--   - encoding: P_∞ the unique pole of x_0, D the sum of all other rational points, n = deg D, b = [F_j : F_0] → IsGSLevel (pole of x_0, injective enumeration of the other rational places), n the number of points, b = relfinrank F_0 F_j; reason: the unique pole is the only place with ord(x_0) < 0; every enumeration gives the same code up to coordinate order
--   - encoding: '(1, e, σ, ε)-CA requires σ ≥ X' → for every real σ, HasCA C 1 e σ ε → X ≤ σ; reason: the meaning of 'requires'
--   - encoding: d(·, C) and d([u_0, u_1], C²) ≥ X; d(C) → codeDist (infimum of Hamming distances); X ≤ interDist to every pair of codewords; minDist (infimum over distinct pairs); reason: the codes are nonempty with at least two codewords, so the infima are the minima
--   - encoding: m = (1 − 2/p^a + 1/p^{3a})qb, e = n − (1 − 1/p^a)qb, exponents (1 − 2/p^a + 1/p^{2a})q and (1 − 1/p^a)q → the same integers as natural-number expressions in P' = p^a and q = P'^{2h}; reason: exact; P' ≥ 2 and n ≥ (q−1)b, so no subtraction truncates
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §5.2, Theorem 5.3, p.36; §2.4, p.15; §5, pp.34–35

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

/-- **Theorem 5.3** (trace counterexample near half the minimum distance; (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §5.2, p.36):
"Let p be a prime, a ≥ 1, h ≥ 2 be integers and set q = p^{2ah}. At a fixed level of the
Garcia-Stichtenoth tower in Section 2.4, let m = (1 − 2/p^a + 1/p^{3a}) qb and
e = n − (1 − 1/p^a) qb, and consider the code C = C_L(D, mP_∞). Set
u_0 = x^{(1−2/p^a+1/p^{2a})q}(D) and u_1 = x^{(1−1/p^a)q}(D). For every z ∈ −(F_q^*)^{p^a−1}, we
have d(r(z), C) = e, while d([u_0, u_1], C^2) ≥ (2 − 1/p^a) e. Consequently, for every
0 ≤ ε < 1 − 1/p^a, (1, e, σ, ε)-CA requires σ ≥ (q−1)/((p^a−1)q). Moreover,
0 < e/n − d(C)/(2n) ≤ 1/(2p^{3a}) and e < (1 − √ρ)n."

**Formalization Note** `F_q` is any finite field with `p^{2ah}` elements; the tower is any
`GSTower` datum over it with `s = p^{ah}` (so `q = s²`), in any ambient field `Ω`, and the level
`j` is arbitrary; `P, Pinf` enumerate the level's evaluation points and its pole of `x_0`
(`IsGSLevel`), `n` is their number and `b = [F_j : F_0]`. With `P' := p^a` and `q = P'^{2h}`, the
integers are written exactly: `m = b(P'^{2h} − 2P'^{2h−1} + P'^{2h−3})`,
`e = n − b(P'^{2h} − P'^{2h−1})`, and the exponents of `u_0`, `u_1` are
`P'^{2h} − 2P'^{2h−1} + P'^{2h−2}` and `P'^{2h} − P'^{2h−1}` (no natural subtraction truncates,
since `P' ≥ 2` and `n ≥ (q−1)b`). `r(z) = u_0 + z u_1` is the base `curve` with `ℓ = 1`;
`−(F_q^*)^{p^a−1}` is `{−w^{p^a−1} : w ≠ 0}`. `d(·, C)` is `codeDist`, `d(C)` the actual minimum
distance `minDist`, `d([u_0, u_1], C²) ≥ X` is "`X ≤` the interleaved distance to every pair of
codewords". "CA requires `σ ≥ X`" is: every real `σ` for which `C` has `(1, e, σ, ε)`-CA satisfies
`X ≤ σ`. `ρ = m/n`; all fractions are real. -/
theorem theorem_5_3 (p a h : ℕ) (hp : p.Prime) (ha : 1 ≤ a) (hh : 2 ≤ h)
    (Fq : Type u) [Field Fq] [Fintype Fq] (hq : Fintype.card Fq = p ^ (2 * a * h))
    (Ω : Type v) [Field Ω] [Algebra Fq Ω] (T : GSTower Fq Ω (p ^ (a * h))) (j : ℕ)
    (n : ℕ) (P : Fin n → Place Fq (T.field j)) (Pinf : Place Fq (T.field j))
    (hlev : IsGSLevel T j P Pinf) :
    let P' : ℕ := p ^ a
    let b : ℕ := T.b j
    let m : ℕ := b * (P' ^ (2 * h) - 2 * P' ^ (2 * h - 1) + P' ^ (2 * h - 3))
    let e : ℕ := n - b * (P' ^ (2 * h) - P' ^ (2 * h - 1))
    let C : Set (Fin n → Fq) := AGProxGap.agCode P Pinf m
    let u : Fin 2 → Fin n → Fq :=
      ![xWord T j P (P' ^ (2 * h) - 2 * P' ^ (2 * h - 1) + P' ^ (2 * h - 2)),
        xWord T j P (P' ^ (2 * h) - P' ^ (2 * h - 1))]
    let q : ℝ := Fintype.card Fq
    (∀ w : Fq, w ≠ 0 → codeDist C (AGProxGap.curve u (-(w ^ (P' - 1)))) = e) ∧
    (∀ c : Fin 2 → Fin n → Fq, (∀ k, c k ∈ C) →
      (2 - 1 / (P' : ℝ)) * e ≤ (AGProxGap.interDist u c : ℝ)) ∧
    (∀ ε : ℝ, 0 ≤ ε → ε < 1 - 1 / (P' : ℝ) → ∀ σ : ℝ, AGProxGap.HasCA C 1 e σ ε →
      (q - 1) / (((P' : ℝ) - 1) * q) ≤ σ) ∧
    0 < (e : ℝ) / n - (minDist C : ℝ) / (2 * n) ∧
    (e : ℝ) / n - (minDist C : ℝ) / (2 * n) ≤ 1 / (2 * (P' : ℝ) ^ 3) ∧
    (e : ℝ) < (1 - Real.sqrt ((m : ℝ) / n)) * n := by sorry

end AGProxGap.Supplement
