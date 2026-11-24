-- Prove2me | solution 1 for erdos_1219
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:54:25.227177+00:00
-- url     : https://prove2.me/submissions/662437d8-6203-4a0e-b3d4-bb2585d93bc7

import Definitions.Def_Erdos1219_Main
import Definitions.Def_Erdos1219_Solution
import Theorems.Thm_Erdos1219_erdos_1219


set_option autoImplicit false
open Cardinal Ordinal
universe u
theorem _root_.solution (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)) :
    Erdos1219.PartitionArrow (Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) (ℵ_ ω) :=
  Erdos1219.erdos_1219 n hn hpow h0
