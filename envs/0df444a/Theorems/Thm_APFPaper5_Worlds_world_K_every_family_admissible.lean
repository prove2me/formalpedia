-- Prove2me | Theorems.Thm_APFPaper5_Worlds_world_K_every_family_admissible
-- name    : APFPaper5.Worlds.world_K_every_family_admissible
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-15T03:47:53.166455+00:00
-- url     : https://prove2.me/theorems/f3a10107-f6f3-4a5e-b025-442962b227b0
-- title:
--   Every finite World K family meets its supplied budget
-- statement:
--   For World K's universal serving relation and cost 1, every finite family is feasible and has infimal bill at most the supplied capacity 1. This is model ledger admissibility, not original executed-protocol admission.
-- source:
--   [{'path': 'source/Theorems/Thm_APFB05_Worlds_one_protocol_keeps_all.lean', 'sha256': 'b4523dde1dcea92f5bb130191bbf3b5033babafa354ce54516aff4d454e98946', 'line': 61, 'declaration': 'APFPaper5.Worlds.world_K_every_family_admissible'}, {'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '2966-3077;3559-3564;3670-3674', 'role': 'Scope boundaries: original readout obligations and finite-resolution versus continuum.'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json', 'revision': '2026-11-14.1', 'role': 'B02 amended finite side realization; B03/B04/B05 unchanged; not certification of supplied source instantiation.'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '2601-2682;2741-2760', 'role': 'Shared support, near-optimal support novelty and guarded marginal-floor scope.'}]

import Definitions.Def_APF_B03_DeclaredInput_r2
import Definitions.Def_APF_B04_DeclaredInput
import Definitions.Def_APF_B05_DeclaredInput_r2
import Definitions.Def_APFB02_EachTakesBothSides

set_option autoImplicit false
namespace APFPaper5.Worlds
end APFPaper5.Worlds
open APFPaper5.Worlds
open APFPaper1.Source

theorem APFPaper5.Worlds.world_K_every_family_admissible (S : Finset ℕ) :
    familyAdmissible (D := ℕ) (P := Unit) (R := Unit) (Record := Unit) (fun _ => ())
      (fun _ => (1 : NNReal)) (fun _ => Set.univ) (fun _ _ _ => True) (fun _ _ _ => True) 1 S := by sorry
