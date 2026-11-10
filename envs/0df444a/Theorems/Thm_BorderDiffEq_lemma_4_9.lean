-- Prove2me | Theorems.Thm_BorderDiffEq_lemma_4_9
-- name    : BorderDiffEq.lemma_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:27:04.450515+00:00
-- url     : https://prove2.me/theorems/323252a3-338e-41e8-95b6-918510b478d1
-- title:
--   Lemma 4.9 — Strassen's division elimination for ABPs, size $O(sR^2)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $K$ be a field of characteristic zero, $x=(x_l)_{l\in\sigma}$ a finite tuple of variables and $y$ one more variable. Let $g(x,y)$ and $h(x,y)$ be computed by ABPs over $K$ of size at most $s$ each and have total degree at most $R$.
--
--   1. If $h(x,0)\ne0$, then there are polynomials $P_i,Q_i\in K[x]$, $0\le i<R$, with $Q_i\ne0$, each computed by an ABP of size at most $C\,s\,(R+1)^2$, such that, with $C_i=P_i/Q_i\in K(x)$,
--   $$
--   \frac{g}{h}\equiv\sum_{i=0}^{R-1}C_i\,y^i\pmod{y^R},\quad\text{i.e.}\quad h\cdot\sum_{i=0}^{R-1}C_iy^i\equiv g\pmod{y^R}\ \text{in } K(x)[y].
--   $$
--   2. If $h\neq0$ and $g/h=q$ is a polynomial, then $q$ is computed by an ABP of size at most $C\,s\,(R+1)^2$.
--
--   The proof of Theorem 2.1 uses part 2 to remove the divisions introduced by Cramer's rule.
--
--   **Formalization Note** The variables $(x,y)$ are `Option σ` with `none` $=y$; `MvPolynomial.optionEquivLeft` views a polynomial as a polynomial in $y$ over $K[x]$, so $h(x,0)$ is its `coeff 0`. ABP sizes count vertices; labels are affine over $K$.
--
--   Differences from the source:
--   - reading: $O(sR^2)$ → $C\,s\,(R+1)^2$ with one absolute $C$ before the field and all parameters; reason: $O(\cdot)$ as an absolute constant; $(R+1)^2$ keeps the bound meaningful at $R=0$ and equals $O(sR^2)$ for $R\ge1$
--   - encoding: "$C_i$ of the form ABP/ABP of size $O(sR^2)$", "$g/h\bmod y^R=\sum C_iy^i$" → $C_i=P_i/Q_i$ with $P_i,Q_i\in K[x]$, $Q_i\ne0$, each with an ABP of that size, and $h\sum C_iy^i\equiv g\pmod{y^R}$ in $K(x)[y]$; reason: $h$ is invertible modulo $y$ over $K(x)$, so the two congruences are equivalent
--   - generalization: the "Moreover" clause under $h(x,0)\ne0$ → under $h\ne0$; reason: $h(x,0)\ne0$ implies $h\ne0$
--   - encoding: "$g/h$ is a polynomial" → $g=h\cdot q$; reason: same condition
--   - encoding: the paper's field $F$ → any field $K$ of characteristic zero; reason: the paper's $F$ is an arbitrary field of characteristic zero, and the lemma is applied over $F(y)$
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.9, p.27 (Lemma 2.6 of [DDS21a])

import Mathlib
import Definitions.Def_BorderDiffEq_ABP

namespace BorderDiffEq

/-- **Lemma 4.9 (Strassen's division elimination; Lemma 2.6 of [DDS21a])**
(Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits via
Differential Equations*, manuscript (STOC 2027 submission), Lemma 4.9, p.27). Let `g(x, y)` and
`h(x, y)` be computed by ABPs of size `s` each and have degree at most `R`, and assume
`h(x, 0) ≠ 0`. Then `g/h mod y^R` can be written as `∑_{i=0}^{R-1} Cᵢ yⁱ`, where each `Cᵢ` is of the
form ABP/ABP of size `O(s R²)`. Moreover, if `g/h` is a polynomial, then it has an ABP of size
`O(s R²)`.

**Formalization Note.** `O(s R²)` is read as `C · s · (R + 1)²` with one absolute `C` quantified
before the field and every parameter (`(R+1)²` keeps the bound meaningful at `R = 0`). Any field `K`
of characteristic zero (applied over `F(y)`), any finite tuple `x` indexed by `σ`; the variables
`(x, y)` are `Option σ` with `none = y`, and `MvPolynomial.optionEquivLeft` views a polynomial as a
polynomial in `y` over `K[x]`, so `h(x, 0)` is its `coeff 0`. First clause: `Cᵢ = Pᵢ / Qᵢ` with
`Pᵢ, Qᵢ ∈ K[x]`, `Qᵢ ≠ 0`, each computed by an ABP over `K` of size at most `C · s · (R+1)²`, and
"`g/h ≡ ∑ Cᵢ yⁱ (mod y^R)`" is `h · ∑ Cᵢ yⁱ ≡ g (mod y^R)` in `K(x)[y]` (equivalent, since `h` is
invertible modulo `y` there). Second clause: "`g/h` is a polynomial" is `g = h * q`; it is stated
under the weaker hypothesis `h ≠ 0` (implied by `h(x, 0) ≠ 0`). -/
theorem lemma_4_9 : ∃ C : ℕ, ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ]
    (s R : ℕ) (g h : MvPolynomial (Option σ) K) (Ag Ah : ABP K (Option σ)),
    Ag.eval = g → Ah.eval = h → Ag.size ≤ s → Ah.size ≤ s →
    g.totalDegree ≤ R → h.totalDegree ≤ R →
    ((MvPolynomial.optionEquivLeft K σ h).coeff 0 ≠ 0 →
      ∃ P Q : Fin R → MvPolynomial σ K,
        (∀ i, Q i ≠ 0) ∧
        (∀ i, ∃ A : ABP K σ, A.eval = P i ∧ A.size ≤ C * s * (R + 1) ^ 2) ∧
        (∀ i, ∃ A : ABP K σ, A.eval = Q i ∧ A.size ≤ C * s * (R + 1) ^ 2) ∧
        Polynomial.X ^ R ∣
          (MvPolynomial.optionEquivLeft K σ h).map
              (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K))) *
            ∑ i : Fin R, Polynomial.C
              (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (P i) /
                algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (Q i)) *
              Polynomial.X ^ (i : ℕ) -
          (MvPolynomial.optionEquivLeft K σ g).map
              (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)))) ∧
    (h ≠ 0 → ∀ q : MvPolynomial (Option σ) K, g = h * q →
      ∃ A : ABP K (Option σ), A.eval = q ∧ A.size ≤ C * s * (R + 1) ^ 2) := by sorry

end BorderDiffEq
