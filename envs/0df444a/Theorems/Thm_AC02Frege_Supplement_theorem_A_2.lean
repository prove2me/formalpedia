-- Prove2me | Theorems.Thm_AC02Frege_Supplement_theorem_A_2
-- name    : AC02Frege.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:00:58.762304+00:00
-- url     : https://prove2.me/theorems/abf97cf9-9a6f-40cf-be7c-dd45aaf160a8
-- title:
--   Theorem A.2 — one-factor gain for an arbitrary $D$-admissible target space
-- statement:
--   Let $C\subseteq V_n$ be a $D$-admissible subspace of the multilinear polynomials over $\mathbb F_2$ in $n$ variables, $D\in\mathbb N\cup\{\infty\}$. Fix a line $L=\bigvee_{i=1}^s(u_i=1)$ with multilinear $u_i$ of degree at most $r$, and a current approximator $P=\prod_\nu q_\nu$, each $q_\nu=1+\sum_i a_{\nu i}u_i$ (products multilinearized). Suppose
--   $$
--   K\ge r,\qquad \deg P+K+2r\le D. \tag{46}
--   $$
--   Then there is $\epsilon\in\mathbb F_2^s$ such that, with $q=1+\sum_i\epsilon_iu_i$ and $P'=Pq$,
--   $$
--   c_{P'}(K)\ \le\ c_P(K)-\tfrac12\,c_P(K-r);
--   $$
--   equivalently, $\dim Z_{P'}(K)\ge\dim Z_P(K)+\tfrac12 c_P(K-r)$.
--
--   Here $Z_P(j)=\{f\in V_j: fPu_i\in C \text{ for every } i\}$ and $c_P(j)=\dim V_j-\dim Z_P(j)$. Appending one well-chosen affine factor to the approximator removes at least half of the error conditions counted at degree $K-r$. The case $C=C_D$ is Pang's Lemma 3.10, and $C=\{0\}$ with $D=\infty$ is the toy model of Appendix A.1.
--
--   Differences from the source:
--   - encoding: V = V_n, functions on the cube identified with multilinear polynomials; the line's polynomials u_i ∈ V_n with deg u_i ≤ r → u_i : MvPolynomial (Fin n) (ZMod 2), multilinear, totalDegree ≤ r; s arbitrary; reason: same instances
--   - encoding: D ∈ ℕ ∪ {∞}; C an F₂-subspace of V_n → D : ℕ∞; C a Submodule of multilinear polynomials with IsAdmissible D C; reason: same instances
--   - encoding: P = ∏_ν q_ν, q_ν = 1 + Σ_i a_{νi} u_i, products multilinearized; P′ = Pq; deg P → P = ML(∏_{ν<t} q_ν) for any t ≥ 0 and a : Fin t → Fin s → ZMod 2; P′ = ML(P · q); deg P = totalDegree of the multilinear P; reason: same instances
--   - encoding: c_P′(K) ≤ c_P(K) − ½ c_P(K − r); equivalently dim Z_P′(K) ≥ dim Z_P(K) + ½ c_P(K − r) → both inequalities, for the same ε, in ℝ; c_P(j) = monoCount n j − finrank(span Z_P(j)); K − r natural subtraction with K ≥ r; reason: same statement
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Theorem A.2, p.36 (proof p.42); Definition A.1, p.35

import Mathlib
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_rankCounts
import Definitions.Def_AC02Frege_Supplement_admissible

namespace AC02Frege.Supplement

open MvPolynomial

/-- Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–Tzameret, *Progress on AC0[2]-Frege Lower
Bounds*, manuscript (sha256 88d149fa…), Theorem A.2, p.36 (one-factor gain, general form; proof
p.42). Fix a `D`-admissible `C`, a line `L = ⋁_{i=1}^s (u_i = 1)` with `deg u_i ≤ r`, and a
current approximator `P = ∏_ν q_ν`, each `q_ν = 1 + Σ_i a_{ν,i} u_i`. Suppose `K ≥ r` and
`deg P + K + 2r ≤ D` (46). Then there is `ε ∈ 𝔽₂^s` such that, with `q = 1 + Σ_i ε_i u_i` and
`P′ = Pq`, `c_{P′}(K) ≤ c_P(K) − ½ c_P(K − r)`; equivalently
`dim Z_{P′}(K) ≥ dim Z_P(K) + ½ c_P(K − r)`.

**Formalization Note** Polynomials are in `n` variables `Fin n`; the `u_i` are multilinear
(elements of `V_n`) of total degree at most `r`, and `s` is arbitrary. `P = ML(∏_{ν<t} q_ν)` for
any number `t ≥ 0` of factors, and `P′ = ML(P q)`; `deg P` is the total degree of the multilinear
`P`. `D ∈ ℕ ∪ {∞}` is `ℕ∞`. Both forms of the conclusion are stated, for the same `ε`, as real
inequalities (`½` is real). `K − r` is natural subtraction, harmless since `K ≥ r`. -/
theorem theorem_A_2 {n s t : ℕ} (D : ℕ∞) (C : Submodule (ZMod 2) (MvPolynomial (Fin n) (ZMod 2)))
    (hC : IsAdmissible D C) (r K : ℕ) (u : Fin s → MvPolynomial (Fin n) (ZMod 2))
    (hu : ∀ i, IsMultilinear (u i) ∧ (u i).totalDegree ≤ r)
    (a : Fin t → Fin s → ZMod 2) (hKr : r ≤ K)
    (hdeg : (((approxProd u a).totalDegree + K + 2 * r : ℕ) : ℕ∞) ≤ D) :
    ∃ ε : Fin s → ZMod 2,
      ((cErrC C u (ML (approxProd u a * (1 + ∑ i, ε i • u i))) K : ℕ) : ℝ) ≤
          (cErrC C u (approxProd u a) K : ℝ) - (cErrC C u (approxProd u a) (K - r) : ℝ) / 2 ∧
      (AC02Frege.dimSpan (ZsolC C u (approxProd u a) K) : ℝ) +
          (cErrC C u (approxProd u a) (K - r) : ℝ) / 2 ≤
        (AC02Frege.dimSpan (ZsolC C u (ML (approxProd u a * (1 + ∑ i, ε i • u i))) K) : ℝ) := by sorry

end AC02Frege.Supplement
