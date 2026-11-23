-- Prove2me | solution 1 for honest_fold_eq_fold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:38:45.620657+00:00
-- url     : https://prove2.me/submissions/04edb368-1d76-470b-b76d-9cf9ef655b30

import Definitions.Def_SimpleRbrFri_Soundness
import Definitions.Def_SimpleRbrFri_Completeness

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (i : Fin P.num_foldings)
    (f : FRI_domain P i → F) (alpha : F) (z : F)
    (hz : z ∈ FRI_domain P (i + 1)) :
    Fold (FRI_domain P i) (P.m i) (extend_by_zero (FRI_domain P i) f) alpha z =
    FRI_honest_fold P i f alpha ⟨z, hz⟩ := rfl
