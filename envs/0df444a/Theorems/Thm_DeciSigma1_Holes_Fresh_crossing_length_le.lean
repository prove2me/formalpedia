-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_crossing_length_le
-- name    : DeciSigma1.Holes.Fresh.crossing_length_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:40.000929+00:00
-- url     : https://prove2.me/theorems/618e6cc7-c544-44e2-8de2-c1f1abd01805
-- title:
--   Fresh: crossing length le
-- statement:
--   An occurrence of a level-`r` marker (`1 ≤ r ≤ t + 1`) that strictly crosses a cut `p` at
--   which a level-`t` marker `τ` ends has at most `|τ|` letters to the left of `p`: otherwise `τ`,
--   or its level-`r` suffix, would occur strictly inside it, against the factor antichain
--   property.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L89-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L89-L112

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}

theorem DeciSigma1.Holes.Fresh.crossing_length_le {W : Fin k → List α} {t r : ℕ} (ht : 1 ≤ t)
    (hr : r ≤ t + 1) {m m0 : Fin k} (hm : m ∈ active W r) (hm0 : m0 ∈ active W t)
    {u : List α} {p e : ℕ} (hτ : marker W t m0 <:+ u.take p) (hμ : marker W r m <:+ u.take e)
    (hpe : p < e) (he : e ≤ u.length) :
    (marker W r m).length ≤ (e - p) + (marker W t m0).length := by sorry
