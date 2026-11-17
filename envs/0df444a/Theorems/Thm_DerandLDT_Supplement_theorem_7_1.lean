-- Prove2me | Theorems.Thm_DerandLDT_Supplement_theorem_7_1
-- name    : DerandLDT.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:37:32.848474+00:00
-- url     : https://prove2.me/theorems/40cd9d44-7c3c-4d4d-89f2-7a2c8a07f60a
-- title:
--   Theorem 7.1 — counterexamples when $k \gg \sqrt q$: lines with slopes in $\mathbb F_{p^{rs}}$ (corrected: $C \ge 1$ in item 4, degree $C\varepsilon\sqrt q$ in item 5)
-- statement:
--   This is the counterexample family of Section 7, showing that the derandomized line-point test needs $q \gg (k/\varepsilon)^2$.
--
--   Let $p$ be a prime and $r, s \ge 1$ integers. Put $e = p^r$, the local agreement parameter $\varepsilon = 1/e = p^{-r}$, $q = p^{2rs}$, $h = p^{rs} = \sqrt q$, and the degree parameter $k = p^{r(s-1)} = \varepsilon\sqrt q$. Let $\mathbb F$ be the field with $q$ elements and $H \subseteq \mathbb F$ its subfield with $h$ elements. Let $\mathcal L = \{\ell_{a,b} : a \in H,\ b \in \mathbb F\}$ be the $hq$ lines of $\mathbb F^2$ whose slope lies in $H$, where $\ell_{a,b}(T) = (T, aT + b)$. There is a constant $C_0 > 0$, independent of all parameters, such that for every such $p, r, s$ there are functions $f_\ell : \ell \to \mathbb F$ $(\ell \in \mathcal L)$ with the following properties.
--
--   1. Each $f_\ell$ agrees on $\ell$ with a univariate polynomial $P_\ell$ of degree at most $k$.
--   2. For independent uniform lines $\ell, \ell' \in \mathcal L$, the probability that they are not parallel and $f_\ell$, $f_{\ell'}$ agree at their intersection point is at least
--   $$\varepsilon - \frac{C_0}{\sqrt q}.$$
--   3. Some trivariate $Q(X, Y, Z)$ of $Z$-degree exactly $1/\varepsilon$ and $(1,1,k)$-weighted degree at most $\sqrt q + 1$ has $Q(T, aT + b, P_{\ell_{a,b}}(T)) = 0$ for every line, yet $Q(X, Y, U(X, Y)) \ne 0$ for every bivariate polynomial $U$.
--   4. For every real $C$ with $1 \le C < \sqrt q$ and every bivariate $g$ of total degree at most $Ck$, with $\ell$ uniform in $\mathcal L$,
--   $$\Pr_\ell[g|_\ell = f_\ell] \le \frac{C}{q}, \qquad \mathbb E_\ell[\mathrm{agree}(g|_\ell, f_\ell)] \le \frac{2C\varepsilon}{\sqrt q}.$$
--   5. Some point table $f : \mathbb F^2 \to \mathbb F$ has $\mathbb E_{\ell \in \mathcal L}[\mathrm{agree}(f|_\ell, f_\ell)] \ge \varepsilon$, and yet, for every real $C > 1$, $\mathrm{agree}(f, g) \le C/\sqrt q$ for every bivariate $g$ of total degree at most $C\varepsilon\sqrt q$.
--
--   Here $g|_\ell = f_\ell$ is equality as functions on the $q$ points of $\ell$, and $\mathrm{agree}$ is the fraction of points of agreement. The theorem complements the goal of the mission (Theorem 1.2): when $q$ is only about $(k/\varepsilon)^2$, local agreement $\varepsilon$ over $\sqrt q$ directions, and even an algebraic certificate of the kind the analysis builds, do not force a global low-degree polynomial with noticeable agreement.
--
--   **Formalization Note** $\mathbb F$ is any finite field with $p^{2rs}$ elements, $H = \{a : a^{h} = a\}$, lines are indexed by $(a, b) \in H \times \mathbb F$ and line functions are functions of the parameter $T$. Variables $X, Y, Z$ are `MvPolynomial (Fin 3)` variables $0, 1, 2$; the weighted-degree bound is membership in the published `LineVsPoint.VD`, and $\mathrm{agree}(f, g)$ is the published `LineVsPoint.agr`. The paper's proof bounds $\mathrm{agree}(f, g)$ in item 5 by $\max(\sqrt q + 1, e \deg g)/q$, which is at most $C/\sqrt q$ only when $C \ge 1 + 1/\sqrt q$; the printed range $C > 1$ is kept.
--
--   Differences from the source:
--   - correction: item 4: for any g of total degree at most Ck for some C < √q → for every real C with 1 ≤ C < √q and every g with totalDegree g ≤ C·k; reason: as printed item 4 is false at C = 0 for every family (fℓ): a constant g = v has degree 0 ≤ 0·k, and the bound E[agree(v, fℓ)] ≤ 0 would hold for every v ∈ F, but each fℓ takes some value; the paper's proof treats C as at least 1 (its family already fails item 4 at g = 0 for every C < 1, since the h lines with b = 0 carry fℓ ≡ 0), and the proof of item 5 says 'for some C ≥ 1'
--   - correction: item 5: every g of total degree at most C√q/ε, where C > 1 → every g with totalDegree g ≤ C·ε·√q (= C·k), for every real C > 1; reason: C√q/ε is a misprint for Cε√q (the proof needs e·deg g ≤ C√q, and Theorem 1.1 states P_{O(k),2}); as printed item 5 is false for every f at (p, r, s) = (3, 1, 1), C = 2: q = 9, the bound is 18 ≥ 2(q − 1) = 16, so the interpolating polynomial of f itself is admitted and agree(f, g) = 1 > 2/3 = C/√q
--   - encoding: item 2: Pr[fℓ(a) = fℓ′(a)] ≥ ε − O(1/√q) → ∃ C₀ > 0, chosen before p, r, s and F, with Pr ≥ ε − C₀/√q; reason: meaning of the O-term: one absolute constant for all parameters
--   - reading: item 2: a is their point of intersection (undefined if the lines are parallel) → a pair with equal slopes (including ℓ = ℓ′) counts as a failure of the event; reason: an undefined event cannot count as a success; this is the stronger reading and the one Claim 7.4's proof bounds
--   - encoding: F = F_q, the finite field of size q := p^{2rs}; 𝓛 = lines whose slope lies in the subfield F_{p^{rs}}; fℓ : ℓ → F_q → every finite field F with card F = p^(2rs); H = {a ∈ F | a^(p^(rs)) = a}; 𝓛 indexed by L = H × F via ℓ_{a,b}(T) = (T, aT + b); fℓ and Pℓ are functions of the parameter T, indexed by F × F and constrained only on L; reason: all fields of size q are isomorphic; H is the unique subfield of size p^{rs}; (a, b) ↦ ℓ_{a,b} is a bijection onto 𝓛 (paper (7.2)), so uniform choices over 𝓛 are uniform over L
--   - encoding: item 3: Z-degree 1/ε, (1,1,k)-degree at most √q + 1, Pℓ a Z-root of the restriction of Q to ℓ, no polynomial Z-root → degreeOf 2 Q = p^r; Q ∈ LineVsPoint.VD F k (√q + 1); Q(T, aT + b, Pℓ(T)) = 0 in F[T]; Q(X, Y, U) ≠ 0 for every U ∈ F[X, Y]; reason: X, Y, Z are the variables 0, 1, 2 of MvPolynomial (Fin 3) F; VD is the published span of the monomials X^iY^jZ^l with i + j + k·l ≤ D
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Theorem 7.1, pp.30–31 (notation and construction p.31, (7.2)–(7.3); proof pp.31–34: Claims 7.4, 7.5, Subclaims 7.6, 7.7)

import Definitions.Def_LineVsPoint_agr
import Definitions.Def_LineVsPoint_VD

set_option autoImplicit false

universe u

namespace DerandLDT.Supplement

open Classical in
/-- **Theorem 7.1** (counterexamples when `k ≫ q^{1/2}`), with two edge corrections.
Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Theorem 7.1, pp.30–31 (proof pp.31–34):
*For every `r, s ∈ ℕ` and prime `p`, let `ε := p^{-r}`, `F = F_q` with `q := p^{2rs}`,
`k := p^{r(s-1)} = ε√q`, and `𝓛` the lines of `F_q²` whose slope lies in the subfield
`F_{p^{rs}}`. Then there are functions `(f_ℓ : ℓ → F_q)_{ℓ∈𝓛}` such that
(1) each `f_ℓ` agrees on `ℓ` with a univariate polynomial `P_ℓ` of degree at most `k`;
(2) for two independent uniform lines `ℓ, ℓ'` of `𝓛` meeting at `a` (undefined if parallel),
`Pr[f_ℓ(a) = f_ℓ'(a)] ≥ ε − O(1/√q)`;
(3) some `Q(X, Y, Z)` of `Z`-degree `1/ε` and `(1,1,k)`-degree at most `√q + 1` has every `P_ℓ`
as a `Z`-root of its restriction to `ℓ`, yet has no polynomial `Z`-root;
(4) every `g(X, Y)` of total degree at most `Ck` (`C < √q`) has `Pr_ℓ[g|ℓ = f_ℓ] ≤ C/q` and
`E_ℓ[agree(g|ℓ, f_ℓ)] ≤ 2Cε/√q`;
(5) some `f : F_q² → F_q` has `E_ℓ[agree(f|ℓ, f_ℓ)] ≥ ε`, yet `agree(f, g) ≤ C/√q` for every
`g(X, Y)` of total degree at most `C√q/ε`, where `C > 1`.*

**Formalization Note.**
* `F` is any finite field of cardinality `p^{2rs}` (all are isomorphic). There is no field with
  one element, so `r = 0` or `s = 0` makes the hypothesis unsatisfiable, as in the paper.
* `e = p^r = 1/ε`, `h = p^{rs} = √q` and `k = p^{r(s-1)}` are definitions, not parameters. The
  subfield `F_{p^{rs}}` is `H = {a ∈ F | a^h = a}`, the unique subfield of `F` of size `h`.
* The lines of `𝓛` are `ℓ_{a,b}(T) = (T, aT + b)` for `(a, b) ∈ H × F` (paper (7.2)); the
  map `(a, b) ↦ ℓ_{a,b}` is injective, so `𝓛` is the finset `L = H ×ˢ F` and uniform choices
  over `𝓛` are uniform over `L`. A function `f_ℓ : ℓ → F` is a function of the parameter `T`:
  `fl (a, b) T` is the value at `(T, aT + b)`. The families `fl` and `P` are indexed by all of
  `F × F`; only the indices in `L` are constrained or averaged.
* Item 2: the two lines meet at the point with `x`-coordinate `t = (b' − b)/(a − a')`; a parallel
  pair (`a = a'`, including `ℓ = ℓ'`) counts as a failure. `O(1/√q)` is an absolute constant
  `C₀`, fixed before `p, r, s`.
* Item 3: variables `X, Y, Z` are `MvPolynomial (Fin 3)` variables `0, 1, 2`. "Z-degree `1/ε`" is
  `degreeOf 2 Q = e`; "(1,1,k)-degree at most `√q + 1`" is membership in the published
  `LineVsPoint.VD F k (√q + 1)`. The restriction of `Q` to `ℓ_{a,b}` with `Z := P_ℓ` is
  `Q(T, aT + b, P_ℓ(T)) ∈ F[T]`. "No polynomial Z-root": `Q(X, Y, U(X, Y)) ≠ 0` for every
  `U ∈ F[X, Y]`.
* Items 4 and 5: `g|ℓ = f_ℓ` is equality as functions on the `q` points of `ℓ`;
  `agree(g|ℓ, f_ℓ)` is the fraction of the `q` parameters `T` at which they agree; `agree(f, g)`
  is the published `LineVsPoint.agr`.
* Correction (item 4): the hypothesis `C < √q` is completed to `1 ≤ C < √q`. At `C = 0` item 4
  is false for every family: a constant `g = v` would need `E[agree(v, f_ℓ)] ≤ 0` for every `v`,
  but every `f_ℓ` takes some value. The proof (Claim 7.5) uses `C ≥ 1`.
* Correction (item 5): the degree bound `C√q/ε` is a typo for `Cε√q = Ck` (the proof needs
  `e·deg g ≤ C√q`, and Theorem 1.1 has `P_{O(k),2}`); as printed it is false at
  `(p, r, s) = (3, 1, 1)`, `C = 2` (`q = 9`, bound `18 ≥ 2(q − 1)`, so the interpolant of `f`
  is admitted and agrees with `f` everywhere). The paper's range `C > 1` is kept. (Its proof
  bounds `agree(f, g)` by `max(√q + 1, e·deg g)/q`, which is `≤ C/√q` only for `C ≥ 1 + 1/√q`;
  the window `1 < C < 1 + 1/√q` is stated as printed, since no counterexample is known.) -/
theorem theorem_7_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ (p r s : ℕ) [Fact p.Prime] (F : Type u) [Field F] [Fintype F],
      Fintype.card F = p ^ (2 * r * s) →
      let q : ℕ := Fintype.card F
      let e : ℕ := p ^ r
      let h : ℕ := p ^ (r * s)
      let k : ℕ := p ^ (r * (s - 1))
      let ε : ℝ := 1 / (e : ℝ)
      let L : Finset (F × F) := (Finset.univ.filter fun a : F => a ^ h = a) ×ˢ Finset.univ
      ∃ (fl : F × F → F → F) (P : F × F → Polynomial F),
        -- Item 1: `f_ℓ` agrees on `ℓ` with `P_ℓ`, of degree at most `k`.
        (∀ ab ∈ L, (P ab).natDegree ≤ k ∧ ∀ T : F, fl ab T = (P ab).eval T) ∧
        -- Item 2: consistency at intersection points, `≥ ε − C₀/√q`.
        (ε - C₀ / Real.sqrt q ≤
          (((L ×ˢ L).filter fun ll : (F × F) × (F × F) =>
              ll.1.1 ≠ ll.2.1 ∧
                fl ll.1 ((ll.2.2 - ll.1.2) / (ll.1.1 - ll.2.1)) =
                  fl ll.2 ((ll.2.2 - ll.1.2) / (ll.1.1 - ll.2.1))).card : ℝ) /
            ((L.card : ℝ) ^ 2)) ∧
        -- Item 3: the trivariate `Q`.
        (∃ Q : MvPolynomial (Fin 3) F,
          Q.degreeOf 2 = e ∧
          Q ∈ LineVsPoint.VD F k (Real.sqrt q + 1) ∧
          (∀ ab ∈ L,
            MvPolynomial.eval₂ Polynomial.C
              ![Polynomial.X, Polynomial.C ab.1 * Polynomial.X + Polynomial.C ab.2, P ab] Q = 0) ∧
          ∀ U : MvPolynomial (Fin 2) F,
            MvPolynomial.bind₁ ![MvPolynomial.X 0, MvPolynomial.X 1, U] Q ≠ 0) ∧
        -- Item 4: low-degree bivariates rarely match a line function.
        (∀ C : ℝ, 1 ≤ C → C < Real.sqrt q →
          ∀ g : MvPolynomial (Fin 2) F, (g.totalDegree : ℝ) ≤ C * k →
            ((L.filter fun ab => ∀ T : F, MvPolynomial.eval ![T, ab.1 * T + ab.2] g = fl ab T).card
                : ℝ) / (L.card : ℝ) ≤ C / q ∧
            (∑ ab ∈ L,
                ((Finset.univ.filter fun T : F =>
                    MvPolynomial.eval ![T, ab.1 * T + ab.2] g = fl ab T).card : ℝ) / (q : ℝ)) /
                (L.card : ℝ) ≤ 2 * C * ε / Real.sqrt q) ∧
        -- Item 5: a point table with local agreement `ε` and low global agreement.
        (∃ f : (Fin 2 → F) → F,
          ε ≤ (∑ ab ∈ L,
                ((Finset.univ.filter fun T : F => f ![T, ab.1 * T + ab.2] = fl ab T).card : ℝ) /
                  (q : ℝ)) / (L.card : ℝ) ∧
          ∀ C : ℝ, 1 < C →
            ∀ g : MvPolynomial (Fin 2) F, (g.totalDegree : ℝ) ≤ C * ε * Real.sqrt q →
              LineVsPoint.agr f g ≤ C / Real.sqrt q) := by sorry

end DerandLDT.Supplement
