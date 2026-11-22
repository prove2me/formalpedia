-- Prove2me | solution 1 for rh_zeta_zero_free_right_half
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T19:03:58.912762+00:00
-- url     : https://prove2.me/submissions/c630bf12-ea0c-488a-841c-92f2e210e6b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_dirichlet_zero_free_bound_below_record
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound

/-!
Reduction (proof-sketch) of `rh_zeta_zero_free_right_half`.

The Riemann zeta function is the Dirichlet L-function of the (unique) character modulo 1
(`DirichletCharacter.LFunction_modOne_eq`), and a point of the open strip
`1/2 < Re s < 1` is never the pole `s = 1`.  So the claim is the modulus-one case of
non-vanishing of Dirichlet L-functions on `1/2 < Re s`.  We split the strip at the verified
boundary `0.8749570698`:

* `0.8749570698 < Re s`: the Proved platform theorem
  `TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound`;
* `Re s ≤ 0.8749570698`: the Open platform theorem
  `GRH.dirichlet_zero_free_bound_below_record` (this is where the whole content sits).

Nothing new about zeta is proved here: the sub-record range for modulus 1 is still the
Riemann hypothesis on that range.
-/

theorem solution (s : ℂ) (h1 : (1 : ℝ) / 2 < s.re) (h2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  -- a point with `Re s < 1` is not the pole
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at h2
  have hpole : ¬ ((1 : DirichletCharacter ℂ 1) = 1 ∧ s = 1) := fun h => hs1 h.2
  -- non-vanishing of the L-function of the character modulo 1, by the two ranges
  have key : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s ≠ 0 := by
    rcases le_or_gt s.re 0.8749570698 with hcap | hcap
    · exact GRH.dirichlet_zero_free_bound_below_record 1 h1 hpole hcap
    · exact TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound 1 hcap hpole
  -- the L-function modulo 1 is the Riemann zeta function
  rwa [DirichletCharacter.LFunction_modOne_eq] at key
