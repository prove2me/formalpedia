-- Prove2me | Theorems.Thm_EdenVerified_planar_singular_value_lemma
-- name    : EdenVerified.planar_singular_value_lemma
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:21:39.299237+00:00
-- url     : https://prove2.me/theorems/8c03dacc-b25d-4c07-aa73-8774fa4261a3
-- title:
--   Eden Verified: planar singular value lemma
-- statement:
--   Manuscript Lemma `lem:sv`: any real angular frequency, every point of the
--   Euclidean plane, and every positive real time, including zero initial radius.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L115-L123
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L115-L123

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.planar_singular_value_lemma (Ω : ℝ) (p : PlanarSpace)
    (t : ℝ) (ht : 0 < t) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      {Real.exp (∫ τ in (0 : ℝ)..t, radialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2)),
       Real.exp (∫ τ in (0 : ℝ)..t, tangentialRate
          (planarEvolution Ω τ p 0 ^ 2 + planarEvolution Ω τ p 1 ^ 2))} := by sorry
