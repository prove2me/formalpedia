-- Prove2me | Theorems.Thm_APFB01_turn_between_same_profile_of_declaredInput
-- name    : APFB01.turn_between_same_profile_of_declaredInput
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:11:28.581771+00:00
-- url     : https://prove2.me/theorems/995309e0-4e19-4913-a485-406273239f3f
-- title:
--   Specialized B01 descent transfers admitted-turn reachability between equal profiles
-- statement:
--   For supplied profile, physical/readout/result truth families and Adm containing the identity, assume APF_B01_DeclaredInput with admissionTruth chosen to mean reachability from x by a map in Adm. Equal profiles of x and y then imply that some map in Adm sends x to y. The theorem assumes this particular B01 instantiation; it does not prove that turn reachability is an original physical admission fact. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFB01_turn_between_same_profile.lean', 'line': 41, 'declaration': 'APFB01.turn_between_same_profile_of_declaredInput', 'sha256': 'b98362c89b28bbe75ec87f7536fbcac4f9cdac0cd5146594c577a17f1c0b354d'}]

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Set.Defs

set_option autoImplicit false

universe uX uP uF uR uO

theorem APFB01.turn_between_same_profile_of_declaredInput {X : Type uX} {Process : Type uP}
    {PhysicalFact : Type uF} {ReadoutFact : Type uR} {ResultFact : Type uO}
    (profile : X → Process → Prop) (truth : PhysicalFact → X → Prop)
    (readoutTruth : ReadoutFact → X → Prop) (resultTruth : ResultFact → X → Prop)
    (Adm : Set (X → X)) (hid : (fun w : X => w) ∈ Adm)
    (hB01 : APF_B01_DeclaredInput profile truth readoutTruth resultTruth
      (fun (x : X) (w : X) => ∃ T ∈ Adm, T x = w))
    (x y : X) (hprof : profile x = profile y) : ∃ T ∈ Adm, T x = y := by sorry
