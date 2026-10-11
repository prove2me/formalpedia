-- Prove2me | Theorems.Thm_BookProof_SmHamiltonian_RealCoeff_sub_prime
-- name    : BookProof.SmHamiltonian.RealCoeff.sub_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:58:11.797371+00:00
-- url     : https://prove2.me/theorems/ff64040a-6c98-4501-9520-c8a1b4cceec7
-- title:
--   BookProof.SmHamiltonian.RealCoeff.sub'
-- statement:
--   BookProof.SmHamiltonian.RealCoeff.sub'

-- Generated from ChapterSmHamiltonian.lean — theorem BookProof.SmHamiltonian.RealCoeff.sub'
import Definitions.Def_ChapterSmOneParticle
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Mathlib
import Definitions.Def_ChapterSmHamiltonian
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.SmHamiltonian



open MvPolynomial
open BookProof.SmOneParticle
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.HermiteProductCore BookProof.FarisLavine
open BookProof.FriedrichsExtension

noncomputable section

theorem BookProof.SmHamiltonian.RealCoeff.sub_prime {d : ℕ} {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p)
    (hq : RealCoeff q) : RealCoeff (p - q) := by sorry
