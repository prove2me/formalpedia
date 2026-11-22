-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_form_add
-- name    : APFPaper5.K1.atomTable_form_add
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:01:53.599658+00:00
-- url     : https://prove2.me/theorems/77c1a5e6-c00c-47ce-bf15-999aeaf73a32
-- title:
--   atomTable form add
-- statement:
--   The form on a recombination is the two forms plus twice the cross term.
--
--   Scope and conditions: Ordinary finite Boolean-record algebra: table entries are epsilon times a count, while the bilinear form on real coefficients is epsilon times a sum of squares. The addition identity holds for arbitrary record weights. Epsilon is an arbitrary real in these identities; positive cost requires its own assumption. The form's real value is not identified with a protocol bill and no physical coefficient space, interface record book or probability law is supplied.
--
--   Exact source statement:
--
--   ```lean
--   theorem atomTable_form_add (w : W → ℝ) (mark : ι → W → Bool) (x y : ι → ℝ) :
--       tableForm (atomTable w mark) (x + y) (x + y) =
--         tableForm (atomTable w mark) x x + tableForm (atomTable w mark) y y +
--           2 * tableForm (atomTable w mark) x y
--   ```
--
--   Source parameters:
--
--   ```lean
--   universe u v
--   variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_the_table_at_one_price:151; USB pullbacks v58 batch A; SHA-256 866a11bd81fa0cce49acb2d1135225aee0b79d3449da4126bdc4344841bead46']

import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper5.K1.atomTable_form_add :
∀ {ι : Type apfNative_u} [inst : Fintype.{apfNative_u} ι] {W : Type apfNative_v} [inst_1 : Fintype.{apfNative_v} W]
  (w : W → Real) (mark : ι → W → Bool) (x y : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_u} ι inst (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark)
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} (ι → Real) (ι → Real) (ι → Real)
        (@instHAdd.{apfNative_u} (ι → Real)
          (@Pi.instAdd.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAdd))
        x y)
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} (ι → Real) (ι → Real) (ι → Real)
        (@instHAdd.{apfNative_u} (ι → Real)
          (@Pi.instAdd.{apfNative_u, 0} ι (fun (a : ι) => Real) fun (i : ι) => Real.instAdd))
        x y))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) x x)
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) y y))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (@APFPaper5.K1.tableForm.{apfNative_u} ι inst
          (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst_1 w mark) x y))) := by sorry
