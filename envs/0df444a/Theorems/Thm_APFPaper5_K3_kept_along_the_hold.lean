-- Prove2me | Theorems.Thm_APFPaper5_K3_kept_along_the_hold
-- name    : APFPaper5.K3.kept_along_the_hold
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:08:26.618359+00:00
-- url     : https://prove2.me/theorems/ced0bc19-9f7e-48fd-a6ad-37bc3ee99824
-- title:
--   Kept along the hold
-- statement:
--   Supporting result: kept along the hold. It holds for exactly the parameters and hypotheses displayed in the attached formal statement. Positive-period states admit repeat undo; an endomap is injective on its periodic states. Finite domains imply eventual periodicity, and invariant predicates persist. A finite separating Boolean family implies a finite domain; a finite process domain gives a quotient instance. Finite state/process type and global separation are explicit assumptions. Finite capacity and a finite carried family alone are not a proof of those assumptions; no continuum or physical repetition claim follows.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1717'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_held_states_and_undo.lean', 'sha256': '09317d508749814bc66fe38131e40d262a4c7555c9b6cb2a91a26b6ff59a135f', 'line': 64, 'declaration': 'APFPaper5.K3.kept_along_the_hold'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1067'}]

import Theorems.Thm_APFB01_physicalState_finite
import Theorems.Thm_APFPaper5_K3_undone_hold_returns
import Theorems.Thm_APFB01_undone_hold_returns_every_object

set_option autoImplicit false

universe uX uP

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.kept_along_the_hold {S : Type*} (D : S → S) (P : S → Prop)
    (hP : ∀ s : S, P s → P (D s)) (o : S) (ho : P o) (n : ℕ) : P (D^[n] o) := by sorry
