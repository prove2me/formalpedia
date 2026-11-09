-- Prove2me | Theorems.Thm_DerandLDT_lemma_6_2
-- name    : DerandLDT.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:31.419067+00:00
-- url     : https://prove2.me/theorems/0c276429-77c3-462a-93fa-d244b95755df
-- title:
--   Lemma 6.2 — interpolation: a nonzero $Q$ of $(1,1,\hat k)$-degree $O(\hat k/\varepsilon^2)$ vanishing on all good lines and points
-- statement:
--   There are absolute constants $c, C \in \mathbb N$ with the following property. Let $0 < \varepsilon \le 1$. For all sufficiently large $q$ (depending on $\varepsilon$), every finite field $\mathbb F$ of size $q$ and all $k, r \in \mathbb N$ with
--   $$
--   q \ge \frac{k^2}{\varepsilon^c}, \qquad r \ge \frac{1}{\varepsilon^c}, \qquad 1 < \frac{\varepsilon r}{20},
--   $$
--   let $U$ be a set of $r$ distinct directions in $\mathbb F^2$, $f : \mathbb F^2 \to \mathbb F$, $(p_L)_L$ a degree-$k$ line table, and let $P' \subseteq \mathbb F^2$ (good points) and $\mathcal L'$ (good lines, along $U$) be such that every good point is accepted by at least $\varepsilon r/10$ good lines and every good line accepts at least $\varepsilon q/10$ good points. Write $\hat k = \max(k, \log_2 q)$. Then there is a nonzero $Q(X, Y, Z) \in \mathbb F[X, Y, Z]$ such that
--
--   1. every monomial $X^i Y^j Z^\ell$ of $Q$ has $i + j + \hat k \ell \le C \hat k/\varepsilon^2$;
--   2. for every good line $L$ with parameterization $a_L + t u_L$, $Q(a_L + t u_L, p_L(t)) \equiv 0$ in $\mathbb F[t]$;
--   3. $Q(a, f(a)) = 0$ for every good point $a$.
--
--   This is the interpolation step of the proof of Theorem 1.2: a single low-degree trivariate polynomial explains the passing of the test on all good lines and points.
--
--   **Formalization Note** "Good" points and lines are any sets with the degree properties of the subgraph of Corollary 6.1; the restriction to a line is `LineVsPoint.graphRestrict`, and $Q(a, f(a))$ is evaluation at $(a_0, a_1, f(a))$.
--
--   Differences from the source:
--   - reading: Lemma 6.2 inside Section 6, whose standing regime is Theorem 1.2's hypotheses with r = (1/ε)^c "for a large enough c", ε ∈ (0,1] "an arbitrary constant", and Claim 6.3 "for all sufficiently large q" including its bullet 1 < εr/20 → ∃ c C, ∀ ε ∈ (0,1], ∃ q₀, hypotheses q ≥ q₀, q ≥ k²/ε^c, r ≥ 1/ε^c and 20 < εr; reason: the section's standing assumptions are hypotheses of the lemma; εr > 20 is not implied by r ≥ 1/ε^c when ε is close to 1
--   - reading: (1, 1, k̂)-degree at most O(k̂/ε²) → every monomial has i + j + k̂ℓ ≤ C·k̂/ε² with an absolute constant C; reason: the O(·) constant is absolute
--   - generalization: good points and lines = the vertex sets of G′ from Corollary 6.1 (with its size bounds), line polynomials from a best-fit table → any P′, L′ ⊆ lines along U with the two minimum-degree properties, and any line table; reason: Corollary 6.1's sets and the best-fit table are instances; the size bounds are not used for the conclusion
--   - encoding: a direction is a nonzero vector up to scalar multiples (u_i, u_j not scalar multiples) → a one-dimensional subspace of F² (finrank 1); r distinct directions = a Finset of r such subspaces; reason: the same object; proportional vectors give one subspace
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Lemma 6.2, p.25, with the parameter regime of Section 6 (Setting parameters and Claim 6.3, p.26)

import Definitions.Def_DerandLDT_linesAlong
import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

universe u

namespace DerandLDT

open Classical in
/-- **Lemma 6.2** (interpolation). Harsha, Kopparty, Kumar, Saptharishi, Sudan, *On derandomizing the line-point low-degree test*,
STOC 2027 submission manuscript (sha256 d57e7d6f…80df), Lemma 6.2, p.25, in the regime of Section 6 (Claim 6.3,
p.26): *There is a nonzero `Q(X, Y, Z) ∈ F[X, Y, Z]` of `(1, 1, k̂)`-degree at most `O(k̂/ε²)`
such that for every good line `L` with line polynomial `g_L`, `Q((X, Y)_L, g_L) ≡ 0`, and
`Q(a, f(a)) = 0` for every good point `a`.* Here `k̂ = max(k, log₂ q)` (p.25).

**Formalization Note.** Good points `P′` and good lines `𝓛′` are any sets with the degree
properties of the subgraph `G′` of Corollary 6.1 (every good point accepted by at least `εr/10`
good lines, every good line accepting at least `εq/10` good points); the size bounds of
Corollary 6.1 are not assumed. `g_L` is the line polynomial `p_L` of the line table `P` (any
table), and `Q((X, Y)_L, g_L) ≡ 0` is `graphRestrict a_L u_L p_L Q = 0` in `F[t]`. The
`O(·)` constant `C` is absolute. The lemma is stated in the standing regime of Section 6: the
hypotheses of Theorem 1.2 for some constant `c` (`r = (1/ε)^c` "for a large enough `c`"),
`ε ∈ (0, 1]`, Claim 6.3's "for all sufficiently large `q`" as `q ≥ q₀(ε)`, and Claim 6.3's
first bullet `1 < εr/20`. The `(1, 1, k̂)`-degree with the real weight `k̂` is the maximum of
`i + j + k̂ℓ` over the monomials `X^i Y^j Z^ℓ` of `Q`. -/
theorem lemma_6_2 :
    ∃ c C : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] (k r : ℕ),
      q₀ ≤ Fintype.card F → (k : ℝ) ^ 2 / ε ^ c ≤ (Fintype.card F : ℝ) →
      1 / ε ^ c ≤ (r : ℝ) → 20 < ε * r →
      ∀ U : Finset (Submodule F (Fin 2 → F)), (∀ u ∈ U, Module.finrank F u = 1) → U.card = r →
      ∀ (f : (Fin 2 → F) → F) (P : LineVsPoint.LineTable F 2 k) (P' : Finset (Fin 2 → F))
        (L' : Finset (LineVsPoint.Line F 2)), L' ⊆ linesAlong U →
        (∀ a ∈ P', ε * r / 10 ≤ ((L'.filter fun L => LineVsPoint.Accepted f P a L).card : ℝ)) →
        (∀ L ∈ L', ε * Fintype.card F / 10 ≤
          ((P'.filter fun a => LineVsPoint.Accepted f P a L).card : ℝ)) →
        ∃ Q : MvPolynomial (Fin 3) F, Q ≠ 0 ∧
          (∀ s ∈ Q.support, ((s 0 + s 1 : ℕ) : ℝ) +
              max (k : ℝ) (Real.logb 2 (Fintype.card F)) * (s 2 : ℝ) ≤
            C * max (k : ℝ) (Real.logb 2 (Fintype.card F)) / ε ^ 2) ∧
          (∀ L ∈ L', LineVsPoint.graphRestrict (P.a L) (P.u L) (P.p L) Q = 0) ∧
          (∀ a ∈ P', MvPolynomial.eval ![a 0, a 1, f a] Q = 0) := by sorry

end DerandLDT
