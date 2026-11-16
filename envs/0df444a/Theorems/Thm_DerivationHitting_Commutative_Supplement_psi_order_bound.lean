-- Prove2me | Theorems.Thm_DerivationHitting_Commutative_Supplement_psi_order_bound
-- name    : DerivationHitting.Commutative.Supplement.psi_order_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:35.968366+00:00
-- url     : https://prove2.me/theorems/a267c785-a8ac-4fd7-a54b-3dd5970a2985
-- title:
--   Lemma 5.11 — Nonvanishing below the exact cutoff
-- statement:
--   Let F be an arbitrary characteristic-zero field, let n,s be nonnegative integers, and let f be a nonzero polynomial in the free associative algebra on n letters over F. Suppose some ncABP with at most s vertices computes f. Affine edge weights and nonhomogeneous inputs are allowed. Define Ψ on words by I∅=1 and I_{xᵢw}=∫₀ᵗ[i/(1+iz)]I_w(z) dz, with formal coefficientwise integration and zero constant term, and extend F-linearly. Its F(t)-linear extension has codomain F((t)). Then
--
--   $$\exists k<ns^2+s:\quad [t^k]\Psi(f)\ne0.$$
--
--   The coefficient window is strict. No injectivity, Wronskian or matrix-detection premise is assumed. Constants are included; their nonzero coefficient is at k=0 whenever an ABP exists. This is the support result for Theorem 5.12.
--
--   Differences from the source:
--   - encoding: variables numbered 1,…,n → variables Fin n with source index i.val+1; reason: a bijective change of indices preserves every coefficient
--   - encoding: finite linear combinations of noncommutative words and ordered path weights → the monoid algebra of the free monoid, with adjacency-power path sums; reason: convolution concatenates words and strictly forward edges bound all paths by m−1 for m vertices
--   - encoding: Ψ(f) is nonzero modulo t^B in the Laurent-series codomain → some coefficient of the power series Ψ(f) at k<B is nonzero; reason: for the stated F-coefficient polynomial input the image lies in F[[t]]; its canonical Laurent embedding preserves these coefficients
--   - generalization: §5.2 adopts a homogeneous working convention for the remainder of the section → general ncABPs, including affine labels; reason: this retains Lemma 5.11's unqualified input wording and the brief's required class, and specializes to every homogeneous instance with the same cutoff
-- source:
--   Shubham Bhardwaj, Foram Lakhani, Partha Mukhopadhyay, Ramprasad Saptharishi, Pratik Shastri, Amit Sinhababu, STOC 2027 submission #577 (October 2026). Canonical submission artifact, not proceedings publication; no arXiv pin. Printed page = PDF page throughout 1–29. pp.20–21, Lemma 5.11.

import Definitions.Def_DerivationHitting_Commutative_Supplement_SeriesData
import Definitions.Def_DerivationHitting_Commutative_Supplement_MatrixData

namespace DerivationHitting.Commutative.Supplement

theorem psi_order_bound {F : Type*} [Field F] [CharZero F] {n s : ℕ}
    (f : NCPoly F n) (hf : f ≠ 0) (hA : ComputableByABP f s) :
    ∃ k : ℕ, k < cutoff n s ∧ PowerSeries.coeff k (psi f) ≠ 0 := by sorry

end DerivationHitting.Commutative.Supplement
