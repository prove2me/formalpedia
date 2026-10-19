-- Prove2me | solution 1 for dusart_theta_mesh_generic_group256
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T01:42:17.068063+00:00
-- url     : https://prove2.me/submissions/06d89eaa-43da-4adf-a455-7b1c7d2c2328

import Definitions.Def_dusart_mesh_upper_group256
theorem solution : DusartNumeric.GenericSpec 2683691264 2700468480 2683649343866428 2700435605508321 := DusartFinitePlain.g256
