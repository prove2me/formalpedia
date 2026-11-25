-- Prove2me | Theorems.Thm_ErdosGirthChromatic_exists_girth_chromaticNumber
-- name    : ErdosGirthChromatic.exists_girth_chromaticNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:41:35.488258+00:00
-- url     : https://prove2.me/theorems/e9df92c5-5b56-4b89-90f1-2a09b452e7f0
-- title:
--   Erdos Girth Chromatic: exists girth chromatic Number
-- statement:
--   **Erdős' theorem (1959).** For every `g` and `k` there is a finite graph with girth greater
--   than `g` and chromatic number greater than `k`.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L52-L54
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Solution.lean#L52-L54

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirth
public import Definitions.Def_Mycielski_Family
public import Definitions.Def_FractionalLib_LarsenProppUllman
public import Definitions.Def_ErdosGirthChromatic_Solution
public import Theorems.Thm_ErdosGirth_exists_girth_chromaticNumber

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirthChromatic

theorem ErdosGirthChromatic.exists_girth_chromaticNumber (g k : ℕ) :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)), (g : ℕ∞) < G.egirth ∧ (k : ℕ∞) < G.chromaticNumber := by sorry
