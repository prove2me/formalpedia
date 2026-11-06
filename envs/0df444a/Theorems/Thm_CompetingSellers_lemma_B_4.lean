-- Prove2me | Theorems.Thm_CompetingSellers_lemma_B_4
-- name    : CompetingSellers.lemma_B_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:50.204524+00:00
-- url     : https://prove2.me/theorems/fe3de930-b5e9-47bb-aa5d-d3e7bb47fb0c
-- title:
--   Lemma B.4 and eq. (16) ($a\ge b$) — the optimum, the constant $c$ and $\varsigma^*$
-- statement:
--   Let $a\ge b$, $\Delta=a-b$, and $c\in(3.146,3.147)$ with $c-\ln c=2$. For every $R\in[0,b]$ there is a unique $s=s(R)\in[R+\Delta,a]$ with $\frac{b+R}{s-\Delta}-\ln\frac b{s-\Delta}=2$ (15). Write $F(R)=a(1-\frac Rb)-b+R\frac b{s(R)-\Delta}$.
--
--   1. If $a/b\ge c$: $F(R)\le\Delta$ for all $R\in[0,b]$, $F(0)=\Delta$, and $\mathrm{opt}_A(a;b)=\Delta$.
--   2. If $a/b<c$: there is a unique $\varsigma^*\in[1,c)$ with $\varsigma^2-\varsigma=\frac ab(1+\ln\varsigma)$; for it, $F(R)\le\Delta+\frac{b^2}{a\varsigma^*}(\varsigma^*-1)(\varsigma^*-\frac ab)^2$ for all $R\in[0,b]$, the maximum is attained at $R=b\,(\frac ba-\frac1{\varsigma^*})(\varsigma^*-1)\in[0,b]$, and
--   $$\mathrm{opt}_A(a;b)=\Delta+\frac{b^2}{a\varsigma^*}(\varsigma^*-1)\Big(\varsigma^*-\frac ab\Big)^2.$$
--
--   This gives Alice's optimal revenue in closed form for $a\ge b$ and is where the threshold $C$ of Theorem 1.1 appears.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - reading: the lemma's sentence without the case hypothesis; §3.3.1 assumes a ≥ b throughout → hypothesis b ≤ a; reason: the section's standing assumption, under which Δ = a − b
--   - reading: eq. (16) ("optA(a; b) ≤ …") together with "the bound is tight" (p.64) → optA S null a b = the right-hand side; reason: (16) and its tightness, proved on pp.63–64
--   - encoding: "the maxima in the two cases are attained at R = 0 and R = b(b/a − 1/ς*)(ς* − 1)" → the value at that R (for its root s) equals the bound, and that R lies in [0, b]; reason: attainment of the maximum; same instances
--   - encoding: "let s be as in Equation (15)" (the unique root) → a conclusion ∃! s for every R ∈ [0, b], and the bounds for every root s; reason: the uniqueness the paper proves before (15); same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma B.4, p.64 (PDF 67); eq. (15) and (16), p.63 (PDF 66); tightness p.64

import Mathlib
import Definitions.Def_CompetingSellers_optA
import Definitions.Def_CompetingSellers_IsLargeAliceEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma B.4 and eq. (16) (`a ≥ b`: the optimum and the constant `c`).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), App. B.3.1, pp.63–64 (PDF 66–67). p.63: "We first show that for all `R ∈ [0, b]`, there is
a unique value `s = s(R) ∈ [R + ∆, a]` that satisfies `(b + R)/(s − ∆) − ln(b/(s − ∆)) = 2`
(15)"; eq. (16): "`optA(a; b) ≤ ∆` if `a/b ≥ c`, and `≤ ∆ + (b²/(aς*)) · (ς* − 1) · (ς* − a/b)²` if
`a/b < c`"; p.64: "the bound is tight". Lemma B.4: "For all `R ∈ [0, b]`, let `s` be as in
Equation (15). Let `c ∈ (3.146, 3.147)` satisfy `c − ln c = 2`. We have:
`a · (1 − R/b) − b + R · b/(s − ∆) ≤ ∆` if `a/b ≥ c`, and
`≤ ∆ + (b²/(aς*)) · (ς* − 1) · (ς* − a/b)²` if `a/b < c`. Here, `ς* ∈ [1, c)` is the unique
value satisfying `ς² − ς = (a/b) · (1 + ln ς)`. Moreover, the maxima in the two cases are
attained at `R = 0` and `R = b · (b/a − 1/ς*) · (ς* − 1)` respectively."

**Formalization Note.** Standing `a ≥ b` (App. B.3.1). Eq. (16) together with its tightness is
the equality `optA(a; b) = ` right-hand side. -/
theorem lemma_B_4 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (c : ℝ) (hc : c ∈ Set.Ioo (3.146 : ℝ) 3.147)
    (hcl : c - Real.log c = 2) :
    (∀ R ∈ Set.Icc (0 : ℝ) b, ∃! s : ℝ, IsSRoot a b R s) ∧
    (c ≤ a / b →
      (∀ R s : ℝ, R ∈ Set.Icc (0 : ℝ) b → IsSRoot a b R s →
        a * (1 - R / b) - b + R * (b / (s - |a - b|)) ≤ |a - b|) ∧
      (∀ s : ℝ, IsSRoot a b 0 s → a * (1 - 0 / b) - b + 0 * (b / (s - |a - b|)) = |a - b|) ∧
      optA S null a b = |a - b|) ∧
    (a / b < c →
      (∃! ς : ℝ, ς ∈ Set.Ico 1 c ∧ ς ^ 2 - ς = a / b * (1 + Real.log ς)) ∧
      ∀ ς : ℝ, ς ∈ Set.Ico 1 c → ς ^ 2 - ς = a / b * (1 + Real.log ς) →
        (∀ R s : ℝ, R ∈ Set.Icc (0 : ℝ) b → IsSRoot a b R s →
          a * (1 - R / b) - b + R * (b / (s - |a - b|)) ≤
            |a - b| + b ^ 2 / (a * ς) * (ς - 1) * (ς - a / b) ^ 2) ∧
        b * (b / a - 1 / ς) * (ς - 1) ∈ Set.Icc (0 : ℝ) b ∧
        (∀ s : ℝ, IsSRoot a b (b * (b / a - 1 / ς) * (ς - 1)) s →
          a * (1 - b * (b / a - 1 / ς) * (ς - 1) / b) - b +
              b * (b / a - 1 / ς) * (ς - 1) * (b / (s - |a - b|)) =
            |a - b| + b ^ 2 / (a * ς) * (ς - 1) * (ς - a / b) ^ 2) ∧
        optA S null a b = |a - b| + b ^ 2 / (a * ς) * (ς - 1) * (ς - a / b) ^ 2) := by sorry

end CompetingSellers
