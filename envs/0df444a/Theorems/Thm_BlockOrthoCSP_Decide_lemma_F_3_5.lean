-- Prove2me | Theorems.Thm_BlockOrthoCSP_Decide_lemma_F_3_5
-- name    : BlockOrthoCSP.Decide.lemma_F_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:14:07.831628+00:00
-- url     : https://prove2.me/theorems/622e1d1c-8653-4067-beac-d5ac95297c43
-- title:
--   Lemma F.3.5 — purified magnitude, product and root-of-unity tests in terms of the original values
-- statement:
--   Let $K$ be the field (F.13) of a finite set $\mathcal F$ of algebraic-valued constraint functions on $D$. Let $F$ be a $K$-valued function on a finite domain, $F'$ any legal singleton purification of $F$, and write $\hat a$ for the purified value of a nonzero value $a$ of $F$. For nonzero values $a, b, c, u$ of $F$,
--   $$|\hat a| = |\hat b| \iff a/b \in \mu(K), \quad |\hat a||\hat u| = |\hat b||\hat c| \iff au/(bc) \in \mu(K) \iff au = \zeta bc \text{ for some } \zeta \in \mu(K),$$
--   $$\hat a\,\hat u = \hat b\,\hat c \iff au = bc,$$
--   and if $a = \rho b$ with $\rho \in \mu(K)$ then $\hat a = \rho\hat b$. These tests turn purified magnitude comparisons into polynomial equations with root-of-unity coefficients.
--
--   **Formalization Note.** The values are taken at points $x_a, x_b, x_c, x_u$ of the domain: $a = F(x_a)$, $\hat a = F'(x_a)$, and so on (purification acts value by value).
--
--   Differences from the source:
--   - encoding: a finite set F of functions f : D^{r_f} → C (C = algebraic complex numbers), r_f ≥ 1 → F : Finset (CFn q) with IsAlgLanguage F (every arity ≥ 1, every value IsAlgebraic ℚ in ℂ); reason: the paper's field C is the algebraic numbers inside ℂ; absolute values and conjugation are those of ℂ
--   - encoding: nonzero values a, b, c, u occurring in F and their purified values â, b̂, ĉ, û → points xa, xb, xc, xu of the domain with G x ≠ 0; a = G xa and â = G' xa; reason: purification maps values to values, so â is G' at any point where G takes the value a
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-14, Lemma F.3.5, Eqs. (F.14)–(F.17)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Purification
import Definitions.Def_BlockOrthoCSP_Decide_NumberField

namespace BlockOrthoCSP.Decide

/-- Lemma F.3.5, p. F-14. The nonzero values `a, b, c, u` are `G xa, G xb, G xc, G xu`, and
their purified values `â, b̂, ĉ, û` are `G' xa, G' xb, G' xc, G' xu`. -/
theorem lemma_F_3_5 {q : ℕ} (hq : 1 ≤ q) (F : Finset (CFn q)) (hF : IsAlgLanguage F)
    {α : Type} [Fintype α] (G G' : α → ℂ) (hK : ∀ x, G x ∈ fieldK F)
    (hG' : IsSingletonPurification G G') (xa xb xc xu : α)
    (ha : G xa ≠ 0) (hb : G xb ≠ 0) (hc : G xc ≠ 0) (hu : G xu ≠ 0) :
    (‖G' xa‖ = ‖G' xb‖ ↔ G xa / G xb ∈ muK F) ∧
    (‖G' xa‖ * ‖G' xu‖ = ‖G' xb‖ * ‖G' xc‖ ↔ G xa * G xu / (G xb * G xc) ∈ muK F) ∧
    (G xa * G xu / (G xb * G xc) ∈ muK F ↔
      ∃ ζ ∈ muK F, G xa * G xu = ζ * (G xb * G xc)) ∧
    (G' xa * G' xu = G' xb * G' xc ↔ G xa * G xu = G xb * G xc) ∧
    (∀ ρ ∈ muK F, G xa = ρ * G xb → G' xa = ρ * G' xb) := by sorry

end BlockOrthoCSP.Decide
