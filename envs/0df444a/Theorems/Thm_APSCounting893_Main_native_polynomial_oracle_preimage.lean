-- Prove2me | Theorems.Thm_APSCounting893_Main_native_polynomial_oracle_preimage
-- name    : APSCounting893.Main.native_polynomial_oracle_preimage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T19:42:19.87307+00:00
-- url     : https://prove2.me/theorems/02a0c8c2-7401-461d-8abf-98006487bcf5
-- title:
--   Polynomial-time word preprocessing before an oracle query
-- statement:
--   Let $A$ be any language of finite binary words and let $f$ be computed by a fixed deterministic binary multitape Turing machine in polynomial time. Then
--
--   $$f^{-1}(A)\in\mathrm{P}^{A}.$$
--
--   The destination is the physical finite oracle-machine model used for the APS counting hierarchy. One fixed machine and one polynomial clock work for every input word, and the oracle receives the actual output word $f(x)$.
--
--   This interface permits uniform gate-address and coefficient-query computations to be performed before calls to lower-level counting-hierarchy languages. Its hypothesis uses actual native Turing-machine computation and a uniform time bound.
-- source:
--   Finite-machine preprocessing interface for the gate-evaluation argument of Andrews, Garg and Schost, Hilbert’s Nullstellensatz is in the Counting Hierarchy, https://arxiv.org/abs/2602.17904, Lemma 6.3, pp. 45–46; used in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. Native finite-machine semantics: https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/PolyTime.lean.

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.native_polynomial_oracle_preimage
    (f : Word → Word)
    (hf : Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
    (A : Language) : InOracleP A (fun x => A (f x)) := by sorry
