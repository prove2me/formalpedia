-- Prove2me | Theorems.Thm_EulerMascheroni_Sondow_finite_cutoff_identity
-- name    : EulerMascheroni.Sondow.finite_cutoff_identity
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:54:43.973737+00:00
-- url     : https://prove2.me/theorems/d27e4fda-75c8-48f4-bc64-5050678b070c
-- title:
--   Finite cutoff evaluation for Sondow integrals
-- statement:
--   For positive integers $n,N$,
--   $$I_n-R_{n,N}=\binom{2n}{n}(H_N-\log N)+L_n-A_n+E_{n,N}.$$
--   This finite identity combines the binomial expansion, integration of the geometric truncation, and the combinatorial identification of the logarithmic form. It is a known source-derived identity awaiting formalization; it assumes no irrationality conjecture.
-- source:
--   J. Sondow, https://arxiv.org/pdf/math/0209070, v2 (2002). Finite evaluation, p. 8, with equations (6), (8), (11), the binomial identities on p. 9, and Lemma 2. The displayed statement is an exact rearrangement for N>0.

import Definitions.Def_eulerMascheroni_sondowCutoff
open EulerMascheroni.Sondow

theorem EulerMascheroni.Sondow.finite_cutoff_identity (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    I n - remainder n N = ((2*n).choose n : ℝ) *
      ((harmonic N : ℝ)-Real.log N) + L n - (A n : ℝ) + cutoffError n N := by sorry
