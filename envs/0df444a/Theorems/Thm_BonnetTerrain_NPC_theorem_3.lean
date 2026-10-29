-- Prove2me | Theorems.Thm_BonnetTerrain_NPC_theorem_3
-- name    : BonnetTerrain.NPC.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T04:20:24.875346+00:00
-- url     : https://prove2.me/theorems/02a45ed0-bab1-437a-93f0-001cfeb17cae
-- title:
--   Theorem 3 — Orthogonal Terrain Guarding is NP-complete
-- statement:
--   The full vertex-guard, full-terrain decision language is NP-complete: it belongs to NP and every language in NP has a polynomial-time many-one reduction to it. The statement is unconditional and has no given reduction, graph-only coverage premise or bounded-grid restriction.
--
--   Differences from the source:
--   - encoding: finite descriptions of terrain coordinates and an integer budget → self-delimiting binary codes of a positive vertex count, normalized signed rational coordinate pairs and a signed integer budget; reason: fixes the finite digit representation implicit on printed pp.26 and 37 while retaining all rational-coordinate inputs and all real edge targets
--   - encoding: simple x-monotone polygonal chains with distinct listed vertices → n edges and n+1 indexed vertices, injectivity, nondecreasing x coordinates and explicit edge-intersection conditions, with closed boundary visibility; reason: represents the nonempty simple-chain convention, permits vertical edges and 180-degree vertices, and rejects malformed inputs
--   - encoding: NP-complete → the published CookPvsNP.NPComplete predicate on the binary decision language; reason: specifies finite-alphabet Turing computation, polynomial certificate length and polynomial-time many-one reductions without changing either clause of the complexity claim
-- source:
--   Bonnet and Giannopoulos (2019), Orthogonal Terrain Guarding is NP-complete, Journal of Computational Geometry 10(2), 21–44, DOI 10.20382/jocg.v10i2a3 (published version), Theorem 3, printed p.25 / PDF p.5; model printed pp.21–22 / PDF pp.1–2; proof printed pp.37–38 / PDF pp.17–18.

import Definitions.Def_BonnetTerrain_NPC_DecisionLanguage

namespace BonnetTerrain.NPC

theorem theorem_3 :
    CookPvsNP.NPComplete BonnetTerrain.NPC.orthogonalTerrainLanguage := by sorry

end BonnetTerrain.NPC
