-- Prove2me | Theorems.Thm_DerandLDT_theorem_1_2
-- name    : DerandLDT.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:09:46.622381+00:00
-- url     : https://prove2.me/theorems/e1d6af96-3432-40e2-abdd-9f2a210b1732
-- title:
--   Theorem 1.2 — local agreement $\varepsilon$ along $r \ge 1/\varepsilon^c$ directions over $q \ge k^2/\varepsilon^c$ gives agreement $\varepsilon^c$ with degree $2k$ (corrected: $r \ge 2$)
-- statement:
--   There is a constant $c \in \mathbb N$ such that the following holds for every $\varepsilon > 0$, every finite field $\mathbb F$ of size $q$ and all natural numbers $k, r$ with
--   $$
--   q \ge \frac{k^2}{\varepsilon^c}, \qquad r \ge \frac{1}{\varepsilon^c}, \qquad r \ge 2 .
--   $$
--   Let $U$ be a set of $r$ distinct directions in $\mathbb F^2$ and $\mathcal L$ the set of the $rq$ lines along these directions. Then for every $f : \mathbb F^2 \to \mathbb F$,
--   $$
--   \mathbb E_{\ell \in \mathcal L}\big[\mathrm{agree}(f|_\ell, \mathcal P_{k,1})\big] \ge \varepsilon \quad \Longrightarrow \quad \mathrm{agree}(f, \mathcal P_{2k,2}) \ge \varepsilon^c .
--   $$
--   Here $\mathrm{agree}(g, \mathcal F) = \max_{h \in \mathcal F} \Pr_z[g(z) = h(z)]$ for a uniform point $z$, $\mathcal P_{k,1}$ is the space of univariate polynomials of degree at most $k$ and $\mathcal P_{2k,2}$ the space of bivariate polynomials of total degree at most $2k$.
--
--   This is the main theorem of the paper: a high-error analysis of the line-point low-degree test that uses lines in only $\mathrm{poly}(1/\varepsilon)$ directions, provided the field is quadratically large in the degree.
--
--   **Formalization Note** The hypothesis is stated as the existence of a degree-$k$ line table whose local agreement along $U$ (`DerandLDT.localAgr`) is at least $\varepsilon$; this is equivalent to the printed average of per-line maxima. The conclusion asks for a bivariate polynomial of total degree at most $2k$ agreeing with $f$ on at least an $\varepsilon^c$ fraction of $\mathbb F^2$ (`LineVsPoint.agr`).
--
--   Differences from the source:
--   - correction: q ≥ k²/ε^c and r ≥ 1/ε^c → additionally r ≥ 2; reason: at ε = 1 the printed hypotheses allow r = 1 and the statement is false for every c: over F₂ with k = 0, U the vertical direction and f(x, y) = x, every vertical line carries a constant (local agreement 1) while every constant agrees with f on half of F₂² (checked in Lean); for ε < 1 and c ≥ 1, r ≥ 1/ε^c already gives r ≥ 2
--   - encoding: a direction is a nonzero vector up to scalar multiples (u_i, u_j not scalar multiples) → a one-dimensional subspace of F² (finrank 1); r distinct directions = a Finset of r such subspaces; reason: the same object; proportional vectors give one subspace
--   - encoding: E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})] ≥ ε (average of per-line maxima) → ∃ a degree-k line table P with localAgr f P U ≥ ε; reason: every line has q points and the per-line maximum is attained, so the best table attains the average of maxima; affine reparameterization preserves degree
--   - encoding: agree(f, P_{2k,2}) ≥ ε^c → ∃ Q ∈ F[X, Y] with totalDegree Q ≤ 2k and agr f Q ≥ ε^c; reason: the maximum over the finite-valued agreements is attained
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 1.2, p.5 (restated p.24)

import Definitions.Def_DerandLDT_localAgr
import Definitions.Def_LineVsPoint_agr

set_option autoImplicit false

universe u

namespace DerandLDT

/-- **Theorem 1.2** (analysis of the derandomized line-point test), corrected with `r ≥ 2`.
Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Theorem 1.2, p.5 (restated p.24): *There is a constant `c ∈ ℕ` such that for every
`ε > 0`, every finite field `F` of size `q`, and all `k, r ∈ ℕ` with `q ≥ k²/ε^c` and
`r ≥ 1/ε^c`: if `U` is a set of `r` distinct directions in `F²` and `𝓛` the set of all lines
along them, then for every `f : F² → F`, `E_{ℓ∈𝓛}[agree(f|ℓ, P_{k,1})] ≥ ε` implies
`agree(f, P_{2k,2}) ≥ ε^c`.*

**Formalization Note.** Directions are one-dimensional subspaces of `F²` (`finrank F u = 1`), so
"`r` distinct directions" is a `Finset` of `r` such subspaces. The hypothesis
`E_ℓ[agree(f|ℓ, P_{k,1})] ≥ ε` is `∃ P : LineTable F 2 k, ε ≤ localAgr f P U`: the per-line
maximum over degree-`≤ k` polynomials is attained, so choosing the best polynomial on every
line along `U` attains the average of maxima, and the table's parameterization does not matter.
`agree(f, P_{2k,2}) ≥ ε^c` is the existence of a formal bivariate polynomial of total degree
`≤ 2k` agreeing with `f` on an `ε^c` fraction of `F²`. The hypothesis `2 ≤ r` corrects the
printed statement, which is false at `ε = 1`, `r = 1`: over `F₂` with `k = 0`, `U` the
vertical direction and `f(x, y) = x`, every vertical line carries a constant, so the local
agreement is `1`, while every constant agrees with `f` on half of `F₂²`. For `ε < 1` and
`c ≥ 1`, `r ≥ 1/ε^c` already forces `r ≥ 2`. -/
theorem theorem_1_2 :
    ∃ c : ℕ, ∀ ε : ℝ, 0 < ε → ∀ (F : Type u) [Field F] [Fintype F] (k r : ℕ),
      (k : ℝ) ^ 2 / ε ^ c ≤ (Fintype.card F : ℝ) → 1 / ε ^ c ≤ (r : ℝ) → 2 ≤ r →
      ∀ U : Finset (Submodule F (Fin 2 → F)), (∀ u ∈ U, Module.finrank F u = 1) → U.card = r →
      ∀ f : (Fin 2 → F) → F,
        (∃ P : LineVsPoint.LineTable F 2 k, ε ≤ localAgr f P U) →
        ∃ Q : MvPolynomial (Fin 2) F, Q.totalDegree ≤ 2 * k ∧ ε ^ c ≤ LineVsPoint.agr f Q := by sorry

end DerandLDT
