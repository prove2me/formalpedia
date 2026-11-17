-- Prove2me | Theorems.Thm_DSICCompComp_Supplement_theorem_4_1
-- name    : DSICCompComp.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:34:30.492027+00:00
-- url     : https://prove2.me/theorems/1c7c1ed7-2d36-474d-a813-88057a2641b5
-- title:
--   Theorem 4.1 — the optimal DSIC auction needs $\Omega(\sqrt{nm})$ extra bidders to exceed the optimal BIC revenue
-- statement:
--   Sell $m$ independent items to additive bidders whose value vectors are drawn iid from a product distribution $D = D_1 \times \cdots \times D_m$ on $\mathbb R_{\ge 0}^m$. Write $\mathrm{Rev}^{\mathcal D}_N(D)$ for the revenue of the optimal DSIC/IR mechanism with $N$ bidders and $\mathrm{Rev}^{\mathcal B}_n(D)$ for the revenue of the optimal BIC/BIR mechanism with $n$ bidders.
--
--   **Theorem.** There exist absolute constants $\mu > 0$ and $C > 0$ such that for all $n, m$ with $2 \le m \le \mu n$ there is a product distribution $D$ over $m$ items with
--
--   $$
--   \mathrm{Rev}^{\mathcal D}_{n+c}(D) \;<\; \mathrm{Rev}^{\mathcal B}_n(D) \qquad \text{for every integer } 0 \le c < C\sqrt{nm}.
--   $$
--
--   In words: $\Omega(\sqrt{nm})$ additional additive bidders with iid values from $D$ are necessary for the revenue of the best DSIC auction to reach that of the best BIC auction with $n$ bidders. Together with the known $O(\sqrt{nm})$ upper bound for selling separately (a DSIC mechanism), this shows that the DSIC-versus-BIC competition complexity for additive bidders over independent items is $\Theta(\sqrt{nm})$ in this range (Corollary 4.2). The distribution is chosen before $c$; no regularity is required of it.
--
--   **Formalization Note** $\mathrm{Rev}^{\mathcal D}$ is the base mission's published `optRevDSIC` (the published `RevDS`: DSIC and IR at every value profile, measurable payments) and $\mathrm{Rev}^{\mathcal B}$ is `optRevBIC`; both are suprema in $[0, \infty]$.
--
--   Differences from the source:
--
--   - reading: Ω(√nm) additional bidders are necessary for the revenue of the best DSIC auction to exceed that of the best BIC auction → every c ∈ ℕ with c < C·√(nm) has Rev^D_{n+c}(D) < Rev^B_n(D) (strict); reason: the paper uses 'exceed' for ≥ in its own proof (Appendix D, p.37: 'if Rev^D_{n+c} ≥ Rev^B_n, that is, if the revenue of the best DSIC auction ... exceeds that of the best BIC auction ..., then c ≥ Ω(√nm)') and in Definition 2.1; the non-strict reading c < C√(nm) ⇒ Rev^D_{n+c} ≤ Rev^B_n is the weaker one and is satisfied by every point-mass distribution
--   - reading: Ω(√nm) → an absolute constant C > 0, quantified with µ before n and m; reason: standard meaning of Ω, the same shape as the published goal Theorem 3.1
--   - reading: the set 𝒟 of DSIC/IR mechanisms (defined on p.6 without reference to the distribution: DSIC 'for all bidders i, values v_i and v'_i, and value profiles v_{-i}') → the base mission's optRevDSIC (the published RevDS): feasible mechanisms that are DSIC and IR at every value profile in ℝ≥0^{n×m}; reason: the page defines 𝒟 independently of D, quantifying over all values; this is the class the published goal uses
--   - encoding: expected revenue E[Σ_i p_i(v)] of a DSIC/IR mechanism → measurable payments required in RevDS; reason: the expectation is defined only for measurable payments; the convention of the published goal
--   - generalization: ℬ(D): BIC/BIR mechanisms with respect to D → IsAdmissibleBIC: additionally measurable payments and integrable interim-utility integrands; reason: the extra clauses shrink ℬ(D), so Rev^B_n(D) can only decrease; Rev^D_{n+c} < Rev^B_n for the smaller class implies it for the page's class
--   - encoding: E_{v_{-i}∼D^{n-1}}[…] → Bochner integral against the full profile law D^n of an integrand that ignores the i-th coordinate; reason: the i-th coordinate's law is a probability measure, so the two integrals agree
--   - encoding: Rev^M_n(D) and the suprema Rev^D, Rev^B → expRevenueN (∫⁺ − ∫⁻ in EReal) truncated at 0 per mechanism, suprema in ℝ≥0∞; reason: the zero mechanism lies in both classes with revenue 0, so truncation does not change either supremum; same convention as the published goal
--   - encoding: a distribution over m independent items, bidders iid → D : Fin m → ProbabilityMeasure ℝ≥0, profile law Measure.pi (profileLaw); 0-based bidders and items; reason: the base mission's published convention
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Theorem 4.1, p.16 (pdf p.17); BIC/BIR and Rev^B_n, Section 2, pp.5–6 (pdf pp.6–7); 'exceed' as used in Appendix D, p.37 (pdf p.38)

import Mathlib
import Definitions.Def_DSICCompComp_optRevDSIC
import Definitions.Def_DSICCompComp_Supplement_optRevBIC

open MeasureTheory
open scoped NNReal ENNReal

namespace DSICCompComp

namespace Supplement

/-- Theorem 4.1 (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Theorem 4.1, p.16 (pdf p.17)): there exists some constant `µ > 0` such that for all
`2 ≤ m ≤ µn`, there exists a distribution over `m` independent items such that `Ω(√(nm))`
additional additive bidders with iid values from the distribution are necessary for the revenue of
the best DSIC auction to exceed that of the best BIC auction with `n` bidders.

Lean reading: there are absolute constants `µ > 0` and `C > 0` such that for all `n, m` with
`2 ≤ m ≤ µn` there is a product distribution `D = D_1 × ⋯ × D_m` such that every `c ∈ ℕ` with
`c < C√(nm)` has `Rev^𝒟_{n+c}(D) < Rev^B_n(D)`.

**Formalization Note** "Exceed" is `≥`, as the paper's own proof uses it (Appendix D, p.37: "if
`Rev^𝒟_{n+c} ≥ Rev^B_n`, that is, if the revenue of the best DSIC auction ... exceeds that of the
best BIC auction ..., then `c ≥ Ω(√nm)`") and as Definition 2.1 does; so "necessary" is the strict
`<` for every `c < C√(nm)`. The distribution is chosen before `c`; `µ` and `C` before `n`, `m`.
`Rev^𝒟` is the base mission's `optRevDSIC` (the published `RevDS`: DSIC/IR at every profile in
`ℝ≥0^{n×m}`, measurable payments) and `Rev^B` is `optRevBIC`. No regularity is required of `D`. -/
theorem theorem_4_1 :
    ∃ μ : ℝ, 0 < μ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ n m : ℕ, 2 ≤ m → (m : ℝ) ≤ μ * n →
        ∃ D : Fin m → ProbabilityMeasure ℝ≥0,
          ∀ c : ℕ, (c : ℝ) < C * Real.sqrt ((n : ℝ) * m) →
            optRevDSIC (n + c) D < optRevBIC n D := by sorry

end Supplement

end DSICCompComp
