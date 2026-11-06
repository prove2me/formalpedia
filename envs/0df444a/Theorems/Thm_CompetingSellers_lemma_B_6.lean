-- Prove2me | Theorems.Thm_CompetingSellers_lemma_B_6
-- name    : CompetingSellers.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:09:31.855018+00:00
-- url     : https://prove2.me/theorems/4e968ada-a2ce-481d-818b-00ab4ec0b503
-- title:
--   Lemma B.6 (with Lemma B.5's root $u(x)$) — the equalizer ODE and its comparison
-- statement:
--   Let $0<a<b$, $x\in(0,a/b)$ and $\tilde u\in(0,ax/b]$; put $\alpha_{\tilde u}=\frac{b-a}{a-b\tilde u}$ and $s_{\tilde u}=(a-bx)\frac{a-(b-a)\tilde u}{a-(2b-a)\tilde u}$. Then
--
--   1. (Lemma B.5) equation (17) has exactly one root $u=u(x)\in(0,ax/b)$;
--   2. there is a smooth function $U$ on $[s_{\tilde u},a]$ with $U(s_{\tilde u})=(s_{\tilde u}+bx-a)\tilde u$ and, for all $v\in[s_{\tilde u},a]$,
--   $$U'(v)=\frac{v+bx-a}{v+\alpha_{\tilde u}\,(v-U(v))}\qquad(19);$$
--   3. moreover, $u\le\tilde u\iff U(a)\le b\tilde u$, and $u=\tilde u\iff U(a)=b\tilde u$.
--
--   This comparison is how the paper bounds Alice's monopolist utility below by $bu(x)$ in the case $a<b$.
--
--   **Formalization Note** "Smooth" is $C^\infty$ on the closed interval; derivatives at the endpoints are one-sided (`HasDerivWithinAt` on $[s_{\tilde u},a]$).
--
--   Differences from the source:
--   - generalization: ũ = util_Ã(a)/b ∈ (0, ax/b] of the surrounding proof → any ũ ∈ (0, ax/b]; reason: the statement of Lemma B.6 uses nothing about ũ beyond its range, and taking ũ = util_Ã(a)/b specializes it to the source's lemma
--   - reading: "u = u(x) … the unique value that satisfies (17)" (existence and uniqueness from Lemma B.5, pp.68–69) → the conclusion ∃! u, IsURoot a b x u, and the Moreover part for that root; reason: the lemma refers to this u; same instances
--   - encoding: smooth U : [s_ũ, a] → ℝ with z(v) = dU/dv → U : ℝ → ℝ, C^∞ on [s_ũ, a], with HasDerivWithinAt on [s_ũ, a]; reason: values outside the interval are irrelevant; same instances
-- source:
--   Babaioff, Grofman, Lucier, Saxena, On Competing Sellers with Substitutable Goods (manuscript, sha256 75c874b3…), Lemma B.5 and Lemma B.6, p.69 (PDF 72); eqs. (17), (18), p.68 (PDF 71)

import Mathlib
import Definitions.Def_CompetingSellers_IsLargeBobEq

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace CompetingSellers

/-- **Lemma B.6 (the equalizer ODE and its comparison), with Lemma B.5's root `u(x)`.**
Babaioff, Grofman, Lucier, Saxena, *On Competing Sellers with Substitutable Goods*
(manuscript, sha256 75c874b3…), App. B.3.2, pp.68–69 (PDF 71–72). Context: `a < b`, `x ∈ (0, a/b)`, `ũ ∈ (0, ax/b]`,
`α_ũ = (b − a)/(a − bũ)`, `s_ũ` from (18), and `u = u(x) ∈ (0, ax/b)` "the unique value that
satisfies" (17) (existence and uniqueness: Lemma B.5 and p.68–69). "Lemma B.6. There exists a
smooth function `U : [s_ũ, a] → ℝ` such that `U(s_ũ) = (s_ũ + bx − a) · ũ` and, denoting
`z(v) = dU(v)/dv`, we have for all `v ∈ [s_ũ, a]` that: `z(v) = (v + bx − a)/(v + α_ũ ·
(v − U(v)))` (19). Moreover, we have `u ≤ ũ ⟺ U(a) ≤ bũ` and the left inequality is tight if and
only if the right one is."

**Formalization Note.** "Smooth" is `C^∞` on `[s_ũ, a]`; the derivative is taken within
`[s_ũ, a]` (one-sided at the endpoints). `ũ` is any number in `(0, ax/b]` (the lemma uses
nothing else about it). -/
theorem lemma_B_6 (a b x ut : ℝ) (ha : 0 < a) (hab : a < b) (hx : x ∈ Set.Ioo 0 (a / b))
    (hut : ut ∈ Set.Ioc 0 (a * x / b)) :
    (∃! u : ℝ, IsURoot a b x u) ∧
    ∃ U : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U (Set.Icc (sU a b x ut) a) ∧
      U (sU a b x ut) = (sU a b x ut + b * x - a) * ut ∧
      (∀ v ∈ Set.Icc (sU a b x ut) a,
        HasDerivWithinAt U ((v + b * x - a) / (v + alphaU a b ut * (v - U v)))
          (Set.Icc (sU a b x ut) a) v) ∧
      ∀ u : ℝ, IsURoot a b x u → ((u ≤ ut ↔ U a ≤ b * ut) ∧ (u = ut ↔ U a = b * ut)) := by sorry

end CompetingSellers
