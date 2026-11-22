-- Prove2me | solution 1 for polychromColouringBound_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:53.8217+00:00
-- url     : https://prove2.me/submissions/323779b6-773b-4d24-8c86-94ada96fe37e

import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.NNRat.Floor
import Mathlib.Tactic.Rify
import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_Compactness
import Definitions.Def_Polychromatic_LocalLemma
import Definitions.Def_Polychromatic_Existence
import Theorems.Thm_polychromColouringBound_succ

set_option autoImplicit true
open Finset
open Pointwise
variable {G : Type*} [AddCommGroup G]
open MeasureTheory ProbabilityTheory
open Real
theorem _root_.solution {k m m' : ℕ} (hk : k ≠ 0) (h : 2 * k ≤ m + 1)
    (hm' : m ≤ m') (hkm : polychromColouringBound k m) :
    polychromColouringBound k m' := by
  have : MonotoneOn (polychromColouringBound k) {m | 2 * k - 1 ≤ m} :=
    monotoneOn_nat_Ici_of_le_succ fun x hx ↦ polychromColouringBound_succ hk (by lia)
  exact this (by grind) (by grind) hm' hkm
