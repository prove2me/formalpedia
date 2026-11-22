-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_form_at_one_price
-- name    : APFPaper5.K1.atomTable_form_at_one_price
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:02:10.9197+00:00
-- url     : https://prove2.me/theorems/b24f939a-4d6f-44a2-b0c4-6ca74d51670b
-- title:
--   atomTable form at one price
-- statement:
--   With every record at epsilon, the form of the table on a combination is epsilon times a sum of
--   squares, one for each record.
--
--   Scope and conditions: Ordinary finite Boolean-record algebra: table entries are epsilon times a count, while the bilinear form on real coefficients is epsilon times a sum of squares. The addition identity holds for arbitrary record weights. Epsilon is an arbitrary real in these identities; positive cost requires its own assumption. The form's real value is not identified with a protocol bill and no physical coefficient space, interface record book or probability law is supplied.
--
--   Exact source statement:
--
--   ```lean
--   theorem atomTable_form_at_one_price (eps : ℝ) (mark : ι → W → Bool) (x : ι → ℝ) :
--       tableForm (atomTable (fun _ => eps) mark) x x =
--         eps * ∑ a, (∑ i, x i * ind (mark i a)) ^ 2
--   ```
--
--   Source parameters:
--
--   ```lean
--   universe u v
--   variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_the_table_at_one_price:144; USB pullbacks v58 batch A; SHA-256 866a11bd81fa0cce49acb2d1135225aee0b79d3449da4126bdc4344841bead46']

import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper5.K1.atomTable_form_at_one_price :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] {W : Type apfNative_v} [inst_1 : Fintype.{apfNative_v} W]
  (eps : Real) (mark : ι → W → Bool) (x : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
      (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 (fun (x : W) => eps) mark) x x)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
      (@Finset.sum.{apfNative_v, 0} W Real Real.instAddCommMonoid (@Finset.univ.{apfNative_v} W inst_1) fun (a : W) =>
        @HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Finset.sum.{apfNative_u, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_u} ι inst) fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (x i) (APFPaper5.K1.ind (mark i a)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) := by sorry
