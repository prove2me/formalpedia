-- Prove2me | Theorems.Thm_APFPaper5_Worlds_world_K_familyCost
-- name    : APFPaper5.Worlds.world_K_familyCost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:47:50.32011+00:00
-- url     : https://prove2.me/theorems/ef5e9d83-a6cf-4264-aba2-1211eeae58da
-- title:
--   Every finite family costs one in World K
-- statement:
--   For natural-number tasks, one Unit protocol and record, constant whole bill 1, and universal sufficient/use relations, proves the family-cost infimum equals 1 for every finite family, including the empty family.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB05_Worlds_one_protocol_keeps_all.lean', 'sha256': 'b4523dde1dcea92f5bb130191bbf3b5033babafa354ce54516aff4d454e98946', 'line': 34, 'declaration': 'APFPaper5.Worlds.world_K_familyCost'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'role': 'B02 amended finite side realization; B03/B04/B05 unchanged; not certification of supplied source instantiation.'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '2601-2682;2741-2760', 'role': 'Shared support, near-optimal support novelty and guarded marginal-floor scope.'}]

import Definitions.Def_APF_B03_DeclaredInput_r2
import Definitions.Def_APF_B04_DeclaredInput
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false
namespace APFPaper5.Worlds
end APFPaper5.Worlds
open APFPaper5.Worlds
open APFPaper1.Source

theorem APFPaper5.Worlds.world_K_familyCost (S : Finset ℕ) :
    familyCost (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) S
      = 1 := by sorry
