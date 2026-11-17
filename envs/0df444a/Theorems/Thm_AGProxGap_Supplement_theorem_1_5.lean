-- Prove2me | Theorems.Thm_AGProxGap_Supplement_theorem_1_5
-- name    : AGProxGap.Supplement.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:22:42.554896+00:00
-- url     : https://prove2.me/theorems/be5c35cd-4b6f-41dc-bc4c-9f9db6db1733
-- title:
--   Theorem 1.5 — no uniform $O(1/q)$ CA soundness in the Johnson regime on the Garcia–Stichtenoth tower
-- statement:
--   Fix a prime $p$, a slack $0\le\varepsilon<1$ and $\zeta>0$. For every sufficiently large integer $a$ there is $h_0$ such that for every integer $h\ge h_0$, the Garcia–Stichtenoth tower over $\mathbb F_q$ with $q=p^{2ah}$ yields a family of one-point AG codes $C_j=C_L(D_j,m_jP_{\infty,j})$ ($0<m_j<n_j$) of positive asymptotic rate, with block length $n_j\to\infty$, with the following property: for all sufficiently large $j$ there is an integer $e_j\ge0$ such that
--   $$0<\frac{e_j}{n_j}-\frac{d(C_j)}{2n_j}<\zeta,\qquad \frac{e_j}{n_j}<1-\sqrt{\rho_j}\quad(\rho_j=m_j/n_j),$$
--   and nevertheless, if $C_j$ has $(1,e_j,\sigma,\varepsilon)$-CA, then
--   $$\sigma\ge\frac{q-1}{(p^a-1)q}\ge\frac1{2(p^a-1)}.$$
--
--   Fixing an admissible $a$ and letting $h\to\infty$, $q\to\infty$ while the soundness lower bound stays a positive constant: the $O(1/q)$ soundness of Theorem 1.1 below half the designed distance cannot extend through the Johnson regime, even with slack.
--
--   **Formalization Note** Quantifiers in the printed order: $a_0$ depends on $p,\varepsilon,\zeta$; $h_0$ on $a$; the statement then holds for every field with $p^{2ah}$ elements, every tower datum with $s=p^{ah}$ and every choice of level data. Positive asymptotic rate is: some $c>0$ has $\dim C_j/n_j\ge c$ for all large $j$, with $\dim$ the $\mathbb F_q$-dimension. $d(C_j)$ is the actual minimum distance.
--
--   Differences from the source:
--   - encoding: the Garcia–Stichtenoth tower over F_q (x_0 an indeterminate, roots y_{j+1} of y^s + y = x_j^{s+1}) → every GSTower datum in every ambient field Ω ⊇ F_q; reason: Y^s + Y − x_j^{s+1} is irreducible over F_j, so every datum is the tower up to isomorphism
--   - encoding: P_∞ the unique pole of x_0, D the sum of all other rational points, n = deg D, b = [F_j : F_0] → IsGSLevel (pole of x_0, injective enumeration of the other rational places), n the number of points, b = relfinrank F_0 F_j; reason: the unique pole is the only place with ord(x_0) < 0; every enumeration gives the same code up to coordinate order
--   - encoding: d(·, C) and d([u_0, u_1], C²) ≥ X; d(C) → codeDist (infimum of Hamming distances); X ≤ interDist to every pair of codewords; minDist (infimum over distinct pairs); reason: the codes are nonempty with at least two codewords, so the infima are the minima
--   - encoding: positive asymptotic rate; block length n_j → ∞ → ∃ c > 0, eventually c ≤ finrank C_j / n_j; Tendsto n atTop atTop; reason: liminf of the rate is positive iff the rate is eventually bounded below by a positive constant
--   - encoding: 'if C_j has (1, e_j, σ, ε)-CA, then σ ≥ (q−1)/((p^a−1)q) ≥ 1/(2(p^a−1))' → ∀ σ, HasCA C_j 1 e_j σ ε → (q−1)/((p^a−1)q) ≤ σ, and separately 1/(2(p^a−1)) ≤ (q−1)/((p^a−1)q); reason: the second inequality does not depend on σ; together they are the printed chain
--   - encoding: a family of one-point AG codes C_j on the tower → ∃ m : ℕ → ℕ with 0 < m_j < n_j for every j, C_j = agCode (P j) (Pinf j) (m j); reason: §2.3 defines one-point AG codes with 0 < m < n
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §1.1, Theorem 1.5, p.5; formal version Corollary 5.5, p.38; §2.4, p.15

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
import Definitions.Def_AGProxGap_divG
import Definitions.Def_BeatingGV42_goppaCode

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve Filter

universe u v

namespace AGProxGap.Supplement

/-- **Theorem 1.5** (Corollary 5.5; CA cannot be extended to the Johnson regime; (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §1.1,
p.5): "Fix a prime p, a slack 0 ≤ ε < 1, and ζ > 0. For every sufficiently large integer a,
there exists h_0 such that, for every integer h ≥ h_0, the Garcia-Stichtenoth tower over F_q,
with q = p^{2ah}, yields a family of one-point AG codes C_j of positive asymptotic rate, with
block length n_j → ∞. For all sufficiently large j, there exists an integer e_j ≥ 0 such that
0 < e_j/n_j − d(C_j)/(2n_j) < ζ, e_j/n_j < 1 − √ρ_j. Nevertheless, if C_j has (1, e_j, σ, ε)-CA,
then σ ≥ (q−1)/((p^a−1)q) ≥ 1/(2(p^a−1))."

**Formalization Note** Quantifier order as printed: `p, ε, ζ`, then a threshold `a_0` with every
`a ≥ a_0` admissible, then `h_0` (depending on `a`), then every `h ≥ h_0`, every field `F_q` with
`p^{2ah}` elements, every tower datum with `s = p^{ah}` (`q = s²`) and every choice of level data
`IsGSLevel` at every level `j` (`n_j` points, pole `P_{∞,j}`). The family is
`C_j = C_L(D_j, m_j P_{∞,j}) = agCode` for some `m_j` with `0 < m_j < n_j`. Positive asymptotic rate
is "`∃ c > 0` with `dim C_j / n_j ≥ c` for all large `j`" (`dim` = `Module.finrank` of the code
`BeatingGV42.goppaCode`, whose carrier is `agCode`); `n_j → ∞` is `Tendsto`. `d(C_j)` is the actual
minimum distance `minDist`, `ρ_j = m_j/n_j`. The CA lower bound is: every real `σ` for which
`C_j` has `(1, e_j, σ, ε)`-CA satisfies `(q−1)/((p^a−1)q) ≤ σ`; the second inequality
`(q−1)/((p^a−1)q) ≥ 1/(2(p^a−1))` is stated separately. All fractions are real. -/
theorem theorem_1_5 (p : ℕ) (hp : p.Prime) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε < 1) (ζ : ℝ)
    (hζ : 0 < ζ) :
    ∃ a0 : ℕ, ∀ a : ℕ, a0 ≤ a → ∃ h0 : ℕ, ∀ h : ℕ, h0 ≤ h →
      ∀ (Fq : Type u) [Field Fq] [Fintype Fq], Fintype.card Fq = p ^ (2 * a * h) →
      ∀ (Ω : Type v) [Field Ω] [Algebra Fq Ω] (T : GSTower Fq Ω (p ^ (a * h)))
        (n : ℕ → ℕ) (P : ∀ j, Fin (n j) → Place Fq (T.field j))
        (Pinf : ∀ j, Place Fq (T.field j)), (∀ j, IsGSLevel T j (P j) (Pinf j)) →
      ∃ m : ℕ → ℕ, (∀ j, 0 < m j ∧ m j < n j) ∧ Tendsto n atTop atTop ∧
        (∃ c : ℝ, 0 < c ∧ ∀ᶠ j in atTop,
          c ≤ (Module.finrank Fq (BeatingGV42.goppaCode (P j) (AGProxGap.divG (Pinf j) (m j))) : ℝ)
            / n j) ∧
        (∃ j0 : ℕ, ∀ j, j0 ≤ j → ∃ e : ℕ,
          0 < (e : ℝ) / n j - (minDist (AGProxGap.agCode (P j) (Pinf j) (m j)) : ℝ) / (2 * n j) ∧
          (e : ℝ) / n j - (minDist (AGProxGap.agCode (P j) (Pinf j) (m j)) : ℝ) / (2 * n j) < ζ ∧
          (e : ℝ) / n j < 1 - Real.sqrt ((m j : ℝ) / n j) ∧
          ∀ σ : ℝ, AGProxGap.HasCA (AGProxGap.agCode (P j) (Pinf j) (m j)) 1 e σ ε →
            ((Fintype.card Fq : ℝ) - 1) / (((p : ℝ) ^ a - 1) * Fintype.card Fq) ≤ σ) ∧
        1 / (2 * ((p : ℝ) ^ a - 1)) ≤
          ((Fintype.card Fq : ℝ) - 1) / (((p : ℝ) ^ a - 1) * Fintype.card Fq) := by sorry

end AGProxGap.Supplement
