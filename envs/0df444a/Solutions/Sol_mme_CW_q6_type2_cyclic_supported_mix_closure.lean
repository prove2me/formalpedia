-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_supported_mix_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:42:36.549069+00:00
-- url     : https://prove2.me/submissions/17bc3614-2f48-4f81-bf0c-f7523af14b9f

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_type2_cyclic_data

open MME

set_option autoImplicit false
set_option warningAsError true

private def mixedExact
    {N L G : ℕ}
    (x y z : CWQ6ExactCoupledAddress N L G)
    (hsupport : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x.1 y.1 z.1)) :
    CWQ6ExactCoupledAddress N L G :=
  ⟨cwQ6CoupledMixedAddress x.1 y.1 z.1, hsupport, by
    intro i r
    fin_cases i
    · exact x.2.2 0 r
    · exact y.2.2 1 r
    · exact z.2.2 2 r⟩

theorem solution
    {N L G : ℕ}
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupport : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    ∃ e : CWQ6Type2CyclicEdge N L G,
      cwQ6Type2CyclicModeWord e 0 = cwQ6Type2CyclicModeWord x 0 ∧
      cwQ6Type2CyclicModeWord e 1 = cwQ6Type2CyclicModeWord y 1 ∧
      cwQ6Type2CyclicModeWord e 2 = cwQ6Type2CyclicModeWord z 2 := by
  refine ⟨(mixedExact x.1 y.1 z.1 hsupport.1,
      (mixedExact y.2.1 z.2.1 x.2.1 hsupport.2.1,
        mixedExact z.2.2 x.2.2 y.2.2 hsupport.2.2)), ?_⟩
  exact ⟨rfl, rfl, rfl⟩
