-- Prove2me | solution 1 for dusart_theta_mesh_complete_upper_chain
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-17T05:02:47.023336+00:00
-- url     : https://prove2.me/submissions/ed9f7ac1-539f-43ee-b473-2872dc4cc661

import Definitions.Def_dusart_theta_mesh_soundness
import Theorems.Thm_dusart_theta_mesh_generic_interval00
import Theorems.Thm_dusart_theta_mesh_generic_interval01
import Theorems.Thm_dusart_theta_mesh_generic_interval02
import Theorems.Thm_dusart_theta_mesh_generic_interval03
import Theorems.Thm_dusart_theta_mesh_generic_interval04
import Theorems.Thm_dusart_theta_mesh_generic_interval05
import Theorems.Thm_dusart_theta_mesh_generic_interval06
import Theorems.Thm_dusart_theta_mesh_generic_interval07
theorem solution : (1000000 : ℝ) * Chebyshev.theta 100000000 ≤ 99989691935170 →
    (1000000 : ℝ) * Chebyshev.theta 10000064768 ≤ 10000013784295984 ∧
    ∀ x : ℝ, 100000000 ≤ x → x < 10000064768 →
      Chebyshev.theta x ≤ x + 100000 + x / 10000 := by
  apply DusartNumericBridge.generic_to_theta
  intro S step compose
  exact (compose (compose (compose (dusart_theta_mesh_generic_interval00 S step @compose) (dusart_theta_mesh_generic_interval01 S step @compose)) (compose (dusart_theta_mesh_generic_interval02 S step @compose) (dusart_theta_mesh_generic_interval03 S step @compose))) (compose (compose (dusart_theta_mesh_generic_interval04 S step @compose) (dusart_theta_mesh_generic_interval05 S step @compose)) (compose (dusart_theta_mesh_generic_interval06 S step @compose) (dusart_theta_mesh_generic_interval07 S step @compose))))
