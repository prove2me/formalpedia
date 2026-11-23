-- Prove2me | solution 1 for m_dvd_FRI_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:30:47.634573+00:00
-- url     : https://prove2.me/submissions/d21bf635-c952-402c-84fc-d205fac37ca2

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_prod_remaining_m_dvd_FRI_degree

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin P.num_foldings) :
    P.m i ∣ FRI_degree P i :=
  (Finset.dvd_prod_of_mem _ (by grind)).trans <| prod_remaining_m_dvd_FRI_degree P i.val i.isLt.le
