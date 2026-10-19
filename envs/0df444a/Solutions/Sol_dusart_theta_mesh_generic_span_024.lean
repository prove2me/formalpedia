-- Prove2me | solution 1 for dusart_theta_mesh_generic_span_024
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T01:08:58.052306+00:00
-- url     : https://prove2.me/submissions/016c4bef-c4a1-4988-9125-2f7373ee7d6d

import Theorems.Thm_dusart_theta_mesh_generic_group192
import Theorems.Thm_dusart_theta_mesh_generic_group193
import Theorems.Thm_dusart_theta_mesh_generic_group194
import Theorems.Thm_dusart_theta_mesh_generic_group195
import Theorems.Thm_dusart_theta_mesh_generic_group196
import Theorems.Thm_dusart_theta_mesh_generic_group197
import Theorems.Thm_dusart_theta_mesh_generic_group198
import Theorems.Thm_dusart_theta_mesh_generic_group199
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution : DusartNumeric.GenericSpec 1609949440 1744167168 1609919129810472 1744130242829047 := by
 intro S step compose
 exact (compose (compose (compose (dusart_theta_mesh_generic_group192 S step @compose) (dusart_theta_mesh_generic_group193 S step @compose)) (compose (dusart_theta_mesh_generic_group194 S step @compose) (dusart_theta_mesh_generic_group195 S step @compose))) (compose (compose (dusart_theta_mesh_generic_group196 S step @compose) (dusart_theta_mesh_generic_group197 S step @compose)) (compose (dusart_theta_mesh_generic_group198 S step @compose) (dusart_theta_mesh_generic_group199 S step @compose))))
