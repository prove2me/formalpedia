-- Prove2me | solution 1 for polynomial_norm_tendsto_cobounded
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:28:12.276082+00:00
-- url     : https://prove2.me/submissions/d4536e9b-9566-4472-95c6-2b2496054bc1

import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Liouville
open Polynomial Filter Bornology

theorem solution {f : ℂ[X]} (hf : 0 < degree f) : Tendsto (fun z : ℂ => ‖f.eval z‖) (cobounded ℂ) atTop :=
  f.tendsto_norm_atTop hf tendsto_norm_cobounded_atTop
