-- Prove2me | solution 1 for dusart_theta_mesh_generic_interval00
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T04:55:40.490186+00:00
-- url     : https://prove2.me/submissions/7c672018-7e13-483f-9586-e653001476d9

import Definitions.Def_dusart_theta_mesh_compact_interval00
theorem solution : DusartNumeric.GenericSpec 100000000 401989888 99989691935170 401971882499010 := DusartCompactIntervals.interval0_generic
