-- Prove2me | solution 1 for dusart_theta_mesh_generic_group000
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T00:40:24.076987+00:00
-- url     : https://prove2.me/submissions/2e512c3c-d777-4198-86c2-e929b9afdbc2

import Definitions.Def_dusart_mesh_upper_group000
theorem solution : DusartNumeric.GenericSpec 100000000 102097152 99989691935170 102087562006788 := DusartFinitePlain.g0
#print axioms solution
