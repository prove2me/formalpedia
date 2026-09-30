-- Prove2me | solution 1 for liouville_const_of_tendsto_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:28:11.74895+00:00
-- url     : https://prove2.me/submissions/77602a11-954a-4b90-9f0e-db814b7e13cd

import Mathlib.Analysis.Complex.Liouville
open Filter Topology

theorem solution {g : ℂ → ℂ} (hg : Differentiable ℂ g) {c : ℂ} (hgc : Tendsto g (cocompact ℂ) (𝓝 c)) (z : ℂ) : g z = c :=
  hg.apply_eq_of_tendsto_cocompact z hgc
