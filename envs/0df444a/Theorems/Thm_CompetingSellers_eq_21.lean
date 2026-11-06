-- Prove2me | Theorems.Thm_CompetingSellers_eq_21
-- name    : CompetingSellers.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:31.215361+00:00
-- url     : https://prove2.me/theorems/c672934b-bc69-40d1-9faf-0c4cba47f83d
-- title:
--   Eq. (21) and its tightness ($a<b$) — $\mathrm{opt}_A(a;b)=ax^*-bu(x^*)\ge a^2/(4b)$
-- statement:
--   Let $a<b$ and let $u(x)$ denote the root of (17) for $x\in(0,a/b)$. The map $x\mapsto ax-bu(x)$ on $(0,a/b)$ has a unique maximizer $x^*$, and
--   $$\mathrm{opt}_A(a;b)=ax^*-bu(x^*)\ \ge\ \frac{a^2}{4b}>0.$$
--
--   This is Alice's optimal revenue for $a<b$: positive however small her good's value is relative to Bob's.
--
--   Differences from the source:
--   - generalization: one arbitrary uncountable standard Borel message space Σ with a null message ∅ (§2, p.13) → every type S with [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] and an element null : S; reason: the paper fixes one arbitrary such Σ; the statement for every such S specializes to it
--   - reading: the lemma's sentence without the case hypothesis; §3.3.2 assumes a < b throughout → hypothesis a < b; reason: the section's standing assumption, under which Δ = b − a
--   - reading: eq. (21) "optA(a; b) ≤ ax* − bu(x*)" with "the bound … is tight", the uniqueness of the maximizer (p.69) and the guarantee a²/(4b) > 0 (p.71) → existence of a unique maximizer x* (with its root u*), optA = ax* − bu*, and a²/(4b) ≤ optA with 0 < a²/(4b); reason: the displayed result with the claims proved around it; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), App. B.3.2, pp.69–71 (PDF 72–74): eq. (21) and "the bound … is tight", p.70; the a²/(4b) bound, p.71

import Mathlib
import Definitions.Def_CompetingSellers_optA
import Definitions.Def_CompetingSellers_IsLargeBobEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Eq. (21) and its tightness (`a < b`: Alice's optimal revenue).**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), App. B.3.2, pp.69–71 (PDF 72–74): "there must be a value `x* ∈ (0, a/b)` … This implies
that any such point is a maximizer and also implies that the maximizer is unique"; "Overall, we
get that, if `x*` denotes the (unique) maximizer of `ax − bu(x)`, then we have
`optA(a; b) ≤ ax* − bu(x*)`. (21) To finish the proof, we show that the bound on `optA(a; b)`
above is tight"; and p.71: "there is a mechanism that gives her revenue at least `a²/(4b) > 0`".

**Formalization Note.** Standing `a < b`. `u(x)` is the root of (17) (`IsURoot`); the map
`x ↦ ax − bu(x)` on `(0, a/b)` has a unique maximizer `x*`, and `optA(a; b) = ax* − bu(x*)`
(the bound (21) is tight); moreover `optA(a; b) ≥ a²/(4b) > 0`. -/
theorem eq_21 (S : Type) [MeasurableSpace S] [StandardBorelSpace S] [Uncountable S] (null : S)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) :
    ∃ xs us : ℝ, xs ∈ Set.Ioo 0 (a / b) ∧ IsURoot a b xs us ∧
      (∀ x u : ℝ, x ∈ Set.Ioo 0 (a / b) → IsURoot a b x u → a * x - b * u ≤ a * xs - b * us) ∧
      (∀ x u : ℝ, x ∈ Set.Ioo 0 (a / b) → IsURoot a b x u →
        a * x - b * u = a * xs - b * us → x = xs) ∧
      optA S null a b = a * xs - b * us ∧
      a ^ 2 / (4 * b) ≤ optA S null a b ∧ 0 < a ^ 2 / (4 * b) := by sorry

end CompetingSellers
