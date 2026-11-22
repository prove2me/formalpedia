-- Prove2me | Theorems.Thm_APFPaper5_K1_atomTable_at_one_price
-- name    : APFPaper5.K1.atomTable_at_one_price
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T04:00:27.874817+00:00
-- url     : https://prove2.me/theorems/25a7f0e7-b759-47a7-80a9-29bc75211a6b
-- title:
--   atomTable at one price
-- statement:
--   With every record at epsilon, the table's entry for two marks is epsilon times the number of records
--   both are listed against.
--
--   Scope and conditions: Ordinary finite Boolean-record algebra: table entries are epsilon times a count, while the bilinear form on real coefficients is epsilon times a sum of squares. The addition identity holds for arbitrary record weights. Epsilon is an arbitrary real in these identities; positive cost requires its own assumption. The form's real value is not identified with a protocol bill and no physical coefficient space, interface record book or probability law is supplied.
--
--   Exact source statement:
--
--   ```lean
--   omit [Fintype ι] in
--
--   theorem atomTable_at_one_price (eps : ℝ) (mark : ι → W → Bool) (i j : ι) :
--       atomTable (fun _ => eps) mark i j =
--         eps * ((Finset.univ.filter (fun a => mark i a = true ∧ mark j a = true)).card : ℝ)
--   ```
--
--   Source parameters:
--
--   ```lean
--   universe u v
--   variable {ι : Type u} [Fintype ι] {W : Type v} [Fintype W]
--   ```
-- source:
--   ['Theorems.Thm_APFPaper5_K1_the_table_at_one_price:130; USB pullbacks v58 batch A; SHA-256 866a11bd81fa0cce49acb2d1135225aee0b79d3449da4126bdc4344841bead46']

import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
set_option autoImplicit false
universe apfNative_u apfNative_v

theorem APFPaper5.K1.atomTable_at_one_price :
∀ {ι : Type apfNative_u} {W : Type apfNative_v} [inst : Fintype.{apfNative_v} W] (eps : Real) (mark : ι → W → Bool)
  (i j : ι),
  @Eq.{1} Real (@APFPaper5.K1.atomTable.{apfNative_u, apfNative_v} ι W inst (fun (x : W) => eps) mark i j)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) eps
      (@Nat.cast.{0} Real Real.instNatCast
        (@Finset.card.{apfNative_v} W
          (@Finset.filter.{apfNative_v} W
            (fun (a : W) => And (@Eq.{1} Bool (mark i a) Bool.true) (@Eq.{1} Bool (mark j a) Bool.true))
            (fun (a : W) =>
              @instDecidableAnd (@Eq.{1} Bool (mark i a) Bool.true) (@Eq.{1} Bool (mark j a) Bool.true)
                (instDecidableEqBool (mark i a) Bool.true) (instDecidableEqBool (mark j a) Bool.true))
            (@Finset.univ.{apfNative_v} W inst))))) := by sorry
