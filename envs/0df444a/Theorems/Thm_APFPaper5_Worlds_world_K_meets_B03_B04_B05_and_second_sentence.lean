-- Prove2me | Theorems.Thm_APFPaper5_Worlds_world_K_meets_B03_B04_B05_and_second_sentence
-- name    : APFPaper5.Worlds.world_K_meets_B03_B04_B05_and_second_sentence
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:48:52.863196+00:00
-- url     : https://prove2.me/theorems/ca969065-a4b1-414e-a7ca-7d48c328bab5
-- title:
--   An infinite-task model satisfies four stated predicates
-- statement:
--   With one context, tasks ℕ, universal support/use, bill and capacity 1, tested := True and epsilon := 1, proves B03TaskCost, B04FiniteCapacity, MarginalFloor and EveryCombinationHeld on all Boolean assignments. B05 holds because support novelty is absent. Other input predicates and original physical source correspondence are not checked.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB05_Worlds_one_protocol_keeps_all.lean', 'sha256': 'b4523dde1dcea92f5bb130191bbf3b5033babafa354ce54516aff4d454e98946', 'line': 66, 'declaration': 'APFPaper5.Worlds.world_K_meets_B03_B04_B05_and_second_sentence'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'role': 'B02 amended finite side realization; B03/B04/B05 unchanged; not certification of supplied source instantiation.'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '2601-2682;2741-2760', 'role': 'Shared support, near-optimal support novelty and guarded marginal-floor scope.'}]

import Definitions.Def_APF_B03_DeclaredInput_r2
import Definitions.Def_APF_B04_DeclaredInput
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false
namespace APFPaper5.Worlds
end APFPaper5.Worlds
open APFPaper5.Worlds
open APFPaper1.Source

theorem APFPaper5.Worlds.world_K_meets_B03_B04_B05_and_second_sentence :
    APFB03.B03TaskCost (Context := Unit) (D := fun _ => ℕ) (P := fun _ => Unit)
        (R := fun _ => Unit) (Record := fun _ => Unit) (fun _ _ => ())
        (fun _ _ => (1 : NNReal)) (fun _ _ => Set.univ) (fun _ _ _ _ => True)
        (fun _ _ _ _ => True) ∧
    APFB04.B04FiniteCapacity (Context := Unit) (fun _ => 1) ∧
    APFB05.MarginalFloor (Context := Unit) (D := fun _ => ℕ) (P := fun _ => Unit)
        (R := fun _ => Unit) (Record := fun _ => Unit) (fun _ _ => ())
        (fun _ _ => (1 : NNReal)) (fun _ _ => Set.univ) (fun _ _ _ _ => True)
        (fun _ _ _ _ => True) (fun _ _ => True) (fun _ => 1) (fun _ => 1) ∧
    APFB02.EveryCombinationHeld (fun (d : ℕ) (x : ℕ → Bool) => x d) := by sorry
