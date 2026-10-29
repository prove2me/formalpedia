-- Prove2me | Theorems.Thm_BonnetTerrain_NPC_observation_6
-- name    : BonnetTerrain.NPC.observation_6
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T04:19:34.170985+00:00
-- url     : https://prove2.me/theorems/be6feb51-39ec-4934-980a-58a52c911315
-- title:
--   Observation 6 — Downward visibility suffices
-- statement:
--   For every orthogonal terrain and every guarding set of its listed vertices, the same set still guards every real point of the terrain when a guard may only see targets at its own height or below. This retains the printed assertion; the source counterexample is recorded separately in INSIGHTS.yaml.
--
--   Differences from the source:
--   - encoding: an orthogonal terrain and a guarding set at listed vertices → a nonempty indexed real simple polygonal chain satisfying orthogonality, with a finite set of vertex indices and non-strict boundary visibility; reason: represents the discrete guarding convention and all real target points, including vertical sides and straight-through subdivisions
-- source:
--   Bonnet and Giannopoulos (2019), Orthogonal Terrain Guarding is NP-complete, Journal of Computational Geometry 10(2), 21–44, DOI 10.20382/jocg.v10i2a3 (published version), Observation 6, printed p.26 / PDF p.6.

import Definitions.Def_BonnetTerrain_NPC_Geometry

namespace BonnetTerrain.NPC

theorem observation_6
    (T : BonnetTerrain.NPC.Chain) (hT : T.IsTerrain) (hO : T.IsOrthogonal)
    (S : Finset (Fin (T.edgeCount + 1))) (hS : T.Guards S) :
    T.GuardsDownward S := by sorry

end BonnetTerrain.NPC
