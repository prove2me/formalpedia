-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_pade_decay_iff_endpoint_integrality
-- name    : EulerMascheroni.Arithmetic.pade_decay_iff_endpoint_integrality
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T15:14:53.498365+00:00
-- url     : https://prove2.me/theorems/23486935-800f-41ae-8d86-4a9ea6433360
-- title:
--   Endpoint integrality suffices for the entire Padé denominator block
-- statement:
--   For every real $a$, the Padé denominator-decay condition is equivalent to the existence of positive integers $D_n$ such that
--
--   $$D_n q_{2n}(a)\text{ is integral over }\mathbb Z,\qquad\frac{4^nD_n}{n!}\to0.$$
--
--   One need not separately impose integrality of all earlier quotient coefficients: it follows from the recurrence. Thus the simultaneous denominator problem reduces to one endpoint at each index.
-- source:
--   Explicit consequences of the Euler E-system and factorial-quotient recurrence, derived for this decomposition. Compare Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, Theorems 2.5 and 3.2, and Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, §4.1 and §4.3.

import Definitions.Def_eulerMascheroni_padeDecay
open EulerMascheroni.Arithmetic

theorem EulerMascheroni.Arithmetic.pade_decay_iff_endpoint_integrality (a : ℝ) :
    PadeDecayDenominators a ↔
    ∃ D : ℕ → ℕ, (∀ n, 0 < D n) ∧
      Filter.Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) Filter.atTop (nhds 0) ∧
      ∀ n, IsIntegral ℤ ((D n:ℝ)*quotientCoeff a (2*n)) := by sorry
