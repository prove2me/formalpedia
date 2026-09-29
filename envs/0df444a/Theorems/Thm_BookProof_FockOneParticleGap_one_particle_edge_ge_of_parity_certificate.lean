-- Prove2me | Theorems.Thm_BookProof_FockOneParticleGap_one_particle_edge_ge_of_parity_certificate
-- name    : BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:50:49.803773+00:00
-- url     : https://prove2.me/theorems/f2a397e4-282f-4c8b-b459-7a1445296877
-- title:
--   {T P : E →ₗ[ℂ] E} (c : GapCertificate) {thetaE thetaO deltaE deltaO lam : ℝ} (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE) (hEven : sectorGround T P 1 ≤ thetaE + deltaE)...
-- statement:
--   Lean 4 theorem `BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate` (module `BookProof.FockOneParticleGap`), source chapter `BookProof/ChapterFockOneParticleGap.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockOneParticleGap.lean

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
















































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap

theorem BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate {T P : E →ₗ[ℂ] E} (c : GapCertificate)
    {thetaE thetaO deltaE deltaO lam : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hvac : sectorGround T P 1 = 0) (hone : sectorGround T P (-1) = lam) :
    c.lower ≤ lam := by sorry
