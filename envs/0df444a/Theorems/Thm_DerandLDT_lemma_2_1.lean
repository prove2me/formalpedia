-- Prove2me | Theorems.Thm_DerandLDT_lemma_2_1
-- name    : DerandLDT.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:22.58524+00:00
-- url     : https://prove2.me/theorems/3b3f1e3c-080f-44ad-bc1f-4c7d4b63400d
-- title:
--   Lemma 2.1 — lifting consistent roots on parallel lines to a rational root of degree $\le Dk$ (corrected: $\max(k,1)$)
-- statement:
--   There is a constant $c > 0$ such that the following holds for every field $\mathbb F$. Let $Q(X, Y, Z)$ be a nonzero polynomial of $(1, 1, k)$-degree at most $D$, with $Z$-degree $\deg_Z Q$. Let $\mathcal L$ be a finite set of parallel lines in $\mathbb F^2$, and for every $L \in \mathcal L$ let $g_L$ be a polynomial of degree at most $k$ with $Q((X, Y)_L, g_L) \equiv 0$. Let $\hat L$ be a line not parallel to the lines of $\mathcal L$ and $\hat h$ a polynomial of degree at most $k$ such that
--
--   1. $Q((X, Y)_{\hat L}, \hat h) \equiv 0$,
--   2. $(\partial_Z Q)((X, Y)_{\hat L}, \hat h) \not\equiv 0$,
--   3. for every $L \in \mathcal L$, $\hat h$ and $g_L$ agree at the point $L \cap \hat L$.
--
--   If
--   $$
--   |\mathcal L| > c \cdot \deg_Z(Q) \cdot D \cdot \max(k, 1),
--   $$
--   then there is $U(X, Y) \in \mathbb F(X, Y)$ of total degree at most $Dk$ with $Q(X, Y, U(X, Y)) \equiv 0$. Moreover, for all but at most $D$ lines $L \in \mathcal L$, the restriction of $U$ to $L$ is well defined and equals $g_L$.
--
--   This lemma is the technical core of both Theorem 1.2 and the generalized Polishchuk–Spielman lemma: the anchor line $\hat L$ certifies that the roots on the parallel lines are consistent, and they lift to one global rational root.
--
--   **Formalization Note** Every line is read in a fixed parameterization $t \mapsto a_L + t u_L$ (any one); $Q((X, Y)_L, g_L) \equiv 0$ means $Q(a_L + t u_L, g_L(t)) = 0$ in $\mathbb F[t]$, and agreement at $L \cap \hat L$ compares $g_L$ and $\hat h$ at the parameters of the intersection point. $U = \mathrm{num}/\mathrm{den}$ with $\mathrm{den} \neq 0$ and both of total degree at most $Dk$; the root identity holds in the fraction field of $\mathbb F[X, Y]$, and "the restriction of $U$ to $L$ is well defined and equals $g_L$" is $\mathrm{den}|_L \neq 0$ and $\mathrm{num}|_L = \mathrm{den}|_L \cdot g_L$.
--
--   Differences from the source:
--   - correction: |𝓛| > c · (deg_Z(Q) D k) → |𝓛| > c · deg_Z(Q) · D · max(k, 1); reason: the printed threshold is 0 at k = 0 and the statement is then false: Q = (Z − X)(Z − Y) has (1,1,0)-degree 2 and deg_Z 2; with 𝓛 = {x = 1}, g = 1, L̂ = {y = 1}, ĥ = 1 every hypothesis holds ((∂_Z Q)(x, 1, 1) = 1 − x ≠ 0) and 1 > c·0, yet no constant is a Z-root of Q; for k ≥ 1 the thresholds agree
--   - generalization: Q of (1, 1, k)-degree D; ĥ a degree k polynomial; F the field of the paper (usually finite) → (1, 1, k)-degree at most D; deg ĥ ≤ k; any field F and any finite set of parallel lines; reason: the exact-degree and finite-field cases are instances
--   - encoding: Q((X, Y)_L, g_L) ≡ 0 and agreement at L ∩ L̂, without a parameterization → each line read in a fixed parameterization π (any one); agreement at the parameters of the intersection point; reason: the paper notes the property does not depend on the parameterization (p.11)
--   - encoding: U ∈ F(X, Y) of total degree at most Dk; restriction well defined and equal to g_L → U = num/den, den ≠ 0, both of total degree ≤ Dk, identity in the fraction field of F[X, Y]; den|_L ≠ 0 ∧ num|_L = den|_L·g_L; reason: the degree of a rational function is the larger of its numerator's and denominator's (p.10)
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 2.1, p.16 (first stated p.8)

import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace DerandLDT

open Polynomial

open Classical in
/-- **Lemma 2.1** (lifting from consistent parallel lines), corrected threshold. Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point
low-degree test*, STOC 2027 submission manuscript (sha256 d57e7d6f…80df),
Lemma 2.1, p.16 (first stated p.8): *There is a constant `c > 0` such that the following holds.
Let `Q(X, Y, Z)` be a nonzero trivariate polynomial of `(1, 1, k)`-degree `D`. Let `𝓛` be a set of
parallel lines in `F²` such that for every `L ∈ 𝓛` some `g_L` of degree at most `k` satisfies
`Q((X, Y)_L, g_L) ≡ 0`. Let `L̂` be a line not parallel to the lines of `𝓛`, and `ĥ` a degree `k`
polynomial such that `Q((X, Y)_L̂, ĥ)` is identically zero, `(∂_Z Q)((X, Y)_L̂, ĥ)` is nonzero,
and `ĥ` and `g_L` agree at the point `L ∩ L̂` for every `L ∈ 𝓛`. If
`|𝓛| > c·(deg_Z(Q)·D·k)`, then there is `U(X, Y) ∈ F(X, Y)` of total degree at most `Dk` with
`Q(X, Y, U(X, Y)) ≡ 0`. Moreover, for all but at most `D` choices of `L ∈ 𝓛`, the restriction of
`U` to `L` is well defined and equals `g_L`.*

**Formalization Note.** The threshold is corrected to `|𝓛| > c·deg_Z(Q)·D·max(k, 1)`. The
printed threshold fails at `k = 0`: `Q = (Z − X)(Z − Y)` has `(1, 1, 0)`-degree `2` and
`deg_Z Q = 2`; with `𝓛 = {x = 1}`, `g = 1`, `L̂ = {y = 1}`, `ĥ = 1` every hypothesis holds
(`(∂_Z Q)(x, 1, 1) = 1 − x ≠ 0`) and `1 > c·0`, yet no constant (total degree `≤ Dk = 0`) is a
`Z`-root of `Q`. For `k ≥ 1` the two thresholds agree.

Lines are `LineVsPoint.Line F 2` (point sets); the lines of `𝓛` share the direction space `Δ`
and `L̂` has another one. Every line is read in a parameterization `π` (any one): the root on `L`
is `g_L ∈ F[t]` with `graphRestrict a_L u_L g_L Q = 0`, i.e. `Q(a_L + t u_L, g_L(t)) ≡ 0`, and
"agree at `L ∩ L̂`" compares `g_L(t)` and `ĥ(s)` at the parameters of the intersection point.
"Of `(1, 1, k)`-degree `D`" is "at most `D`" (`weightedTotalDegree ![1, 1, k]`), `ĥ` has degree
at most `k`, and `(∂_Z Q)` is `pderiv 2 Q`. `U = num/den` with `den ≠ 0` and both of total degree
at most `Dk`, and `Q(X, Y, U) = 0` holds in the fraction field of `F[X, Y]`; "the restriction of
`U` to `L` is well defined and equals `g_L`" is `den|_L ≠ 0 ∧ num|_L = den|_L·g_L` in `F[t]`.
`F` is any field and `𝓛` any finite set of lines. -/
theorem lemma_2_1 :
    ∃ c : ℝ, 0 < c ∧ ∀ (F : Type u) [Field F] (k D : ℕ) (Q : MvPolynomial (Fin 3) F), Q ≠ 0 →
      MvPolynomial.weightedTotalDegree ![1, 1, k] Q ≤ D →
      ∀ (π : LineVsPoint.LinePar F 2) (Δ : Submodule F (Fin 2 → F))
        (Ls : Finset (LineVsPoint.Line F 2)) (g : LineVsPoint.Line F 2 → F[X]),
        (∀ L ∈ Ls, vectorSpan F L.carrier = Δ) →
        (∀ L ∈ Ls, (g L).natDegree ≤ k ∧ LineVsPoint.graphRestrict (π.a L) (π.u L) (g L) Q = 0) →
        ∀ (Lhat : LineVsPoint.Line F 2) (hhat : F[X]), vectorSpan F Lhat.carrier ≠ Δ →
          hhat.natDegree ≤ k →
          LineVsPoint.graphRestrict (π.a Lhat) (π.u Lhat) hhat Q = 0 →
          LineVsPoint.graphRestrict (π.a Lhat) (π.u Lhat) hhat (MvPolynomial.pderiv 2 Q) ≠ 0 →
          (∀ L ∈ Ls, ∀ t s : F, π.a L + t • π.u L = π.a Lhat + s • π.u Lhat →
            (g L).eval t = hhat.eval s) →
          c * ((Q.degreeOf 2 * D * max k 1 : ℕ) : ℝ) < (Ls.card : ℝ) →
          ∃ num den : MvPolynomial (Fin 2) F, den ≠ 0 ∧
            num.totalDegree ≤ D * k ∧ den.totalDegree ≤ D * k ∧
            MvPolynomial.eval₂
                ((algebraMap (MvPolynomial (Fin 2) F)
                  (FractionRing (MvPolynomial (Fin 2) F))).comp MvPolynomial.C)
                ![algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) (MvPolynomial.X 0),
                  algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) (MvPolynomial.X 1),
                  algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) num /
                    algebraMap (MvPolynomial (Fin 2) F) (FractionRing (MvPolynomial (Fin 2) F)) den] Q = 0 ∧
            (Ls.filter fun L =>
                ¬ (LineVsPoint.lineRestrict (π.a L) (π.u L) den ≠ 0 ∧
                  LineVsPoint.lineRestrict (π.a L) (π.u L) num =
                    LineVsPoint.lineRestrict (π.a L) (π.u L) den * g L)).card ≤ D := by sorry

end DerandLDT
