-- Prove2me | Theorems.Thm_AlmostLinearModComp_Composition_lemma_2_1
-- name    : AlmostLinearModComp.Composition.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:40.250101+00:00
-- url     : https://prove2.me/theorems/96bc51e8-7bd9-4f01-943d-349bd24ff678
-- title:
--   Lemma 2.1 — Coefficient recovery
-- statement:
--   Let $R$ be any commutative ring with identity, $n\ge2$, $f$ a monic polynomial of degree $n$, and $a,g$ polynomials of degree below $n$. Put $N=2^{\lceil\log_2 n\rceil}$ and $F=X^{N-n}f$. Choose any positive number of power-of-two radices $d_i\ge2$ with product $N$, and construct $L$, the digits, the targets $a_i$, and $P$ by equations (1)–(2). Then
--   $$[t^{L-1}]P(a_0,\ldots,a_{m-1})=g(a)\operatorname{rem}F.$$
--
--   The left side is the canonical representative obtained by reducing each $t$-coefficient modulo $F$ and truncating at $t^L$. The equality is of polynomials in $R[X]$, and consequently identifies all $N$ remainder coefficients. This recovers the original composition in the padded quotient, including zero and constant outer or inner polynomials.
--
--   Differences from the source:
--   - encoding: evaluation in S[X]/(F) with S=R[t]/(t^L) → a polynomial in t with coefficientwise canonical remainders in R[X], truncated at L; reason: canonical representatives make coefficient extraction unambiguous and preserve all quotient instances
--   - encoding: power-of-two radices at least two with product N → positive binary exponents on Fin m, with N equal to 2^(Nat.clog 2 n); reason: every source radix list has exactly this encoding; no balance condition is added
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Lemma 2.1, printed p.4 / PDF p.5, with equations (1)–(2), printed p.3 / PDF p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_DigitEncoding

namespace AlmostLinearModComp.Composition

/-- Zhou--Wang, Lemma 2.1 and equations (1)--(2), printed pp.3--4 / PDF pp.4--5.
Equality is of canonical R[X] remainders, not merely quotient classes. -/
theorem lemma_2_1 (R : Type) [CommRing R] (n : ℕ) (hn : 2 ≤ n)
    (f a g : Polynomial R) (hf : f.Monic) (hdeg : f.degree = (n : WithBot ℕ))
    (ha : a.degree < (n : WithBot ℕ)) (hg : g.degree < (n : WithBot ℕ))
    (d : Radices) (hd : d.size = paddedSize n) :
    (encodedEvaluation n d (paddedModulus n d f) a g).coeff (d.precision - 1) =
      g.comp a %ₘ paddedModulus n d f := by sorry

end AlmostLinearModComp.Composition
