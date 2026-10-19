-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_finsum_cexp_trace_sq_div_eq_sqrt_absNorm
-- name    : ArtinPrimitiveRoots.finsum_cexp_trace_sq_div_eq_sqrt_absNorm
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T13:06:26.396818+00:00
-- url     : https://prove2.me/theorems/429dae85-2866-4b9b-9f0b-1577c6328427
-- title:
--   Hecke's quadratic Gauss sum over a number field with no real places — Σ_{x mod α} e(Tr(x²/α)) = √N(α) for α ≡ 1 mod 4𝔇
-- statement:
--   Let $F$ be a number field with no real places (`IsTotallyComplex F`), and let $\alpha \in \mathcal O_F$ with $\alpha - 1 \in 4\mathfrak D_F$, where $\mathfrak D_F$ is the different of $\mathcal O_F$ over $\mathbb Z$ (`differentIdeal ℤ (𝓞 F)`). Then
--   $$\sum_{x \in \mathcal O_F/\alpha\mathcal O_F} \exp\!\Bigl(2\pi i\,\mathrm{Tr}_{F/\mathbb Q}\bigl(\tilde x^2/\alpha\bigr)\Bigr) = \sqrt{\mathrm N(\alpha\mathcal O_F)},$$
--   where $\tilde x$ is any lift of $x$ to $\mathcal O_F$ (here `Quotient.out x`).
--
--   This is a cut for `exists_cutoff_prod_gaussPhase_three_span_eq_one`; that reduction is proved in Lean.
--
--   Classical source: E. Hecke, *Vorlesungen über die Theorie der algebraischen Zahlen* (1923), §54, the reciprocity law for the quadratic Gauss sums of a number field, specialised to the numerator $1$. With no real places the eighth root of unity in Hecke's formula is $1$, and the congruence $\alpha \equiv 1 \pmod{4\mathfrak D}$ makes the dual Gauss sum independent of $\alpha$.
--
--   **Formalization note.** The statement is not in the OpenAI paper. It replaces the paper's Weil-index product formula (3.13) (p. 14) in our proof of the quadratic part of Lemma 3.4.
-- source:
--   E. Hecke, Vorlesungen über die Theorie der algebraischen Zahlen, Akademische Verlagsgesellschaft, Leipzig, 1923, §54 (the reciprocity law of the quadratic Gauss sums: for F with no real places and α ≡ 1 mod 4𝔇, the Gauss sum of x²/α is √N(α)); a cut for exists_cutoff_prod_gaussPhase_three_span_eq_one

import Mathlib

namespace ArtinPrimitiveRoots

open NumberField

theorem finsum_cexp_trace_sq_div_eq_sqrt_absNorm (F : Type*) [Field F] [NumberField F]
    [IsTotallyComplex F] (α : 𝓞 F)
    (hα : α - 1 ∈ Ideal.span {(4 : 𝓞 F)} * differentIdeal ℤ (𝓞 F)) :
    ∑ᶠ x : 𝓞 F ⧸ Ideal.span {α},
        Complex.exp (2 * Real.pi * Complex.I *
          ((Algebra.trace ℚ F (((Quotient.out x : 𝓞 F) : F) ^ 2 / (α : F)) : ℚ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm (Ideal.span {α}) : ℝ) : ℝ) : ℂ)
  := by
  sorry

end ArtinPrimitiveRoots
