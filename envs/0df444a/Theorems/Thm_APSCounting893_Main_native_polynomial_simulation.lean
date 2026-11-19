-- Prove2me | Theorems.Thm_APSCounting893_Main_native_polynomial_simulation
-- name    : APSCounting893.Main.native_polynomial_simulation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T18:26:42.107652+00:00
-- url     : https://prove2.me/theorems/a621f8fb-4899-417e-919e-9f64c7dc06e1
-- title:
--   Transfer of native polynomial-time machines to physical oracle machines
-- statement:
--   Let $A$ be any oracle language. Native deterministic polynomial-time computations over binary words transfer to the finite oracle-machine model:
--
--   $$\operatorname{NativePolyTime}(f)\Longrightarrow f\in\mathrm{FP}^{A},$$
--
--   and, for a Boolean-valued function $b$,
--
--   $$\operatorname{NativePolyTime}(b)\Longrightarrow\{x:b(x)=\mathrm{true}\}\in\mathrm{P}^{A}.$$
--
--   The native input encoding is the word itself; its Boolean output encoding is a singleton word. Native polynomial time means a fixed deterministic binary multitape machine with finitely many states and polynomially bounded transition count. The destination uses the actual finite oracle machines of this development, and word-valued outputs are read from the charged physical output tape. The same destination machine and polynomial handle every input length. No oracle is needed by the transferred computations, so the conclusion holds for every $A$.
--
--   This interface permits the reusable native arithmetic, list and bounded-iteration algorithms to be used in the circuit and certificate procedures of Section 6.
-- source:
--   Model-transfer implementation for the finite machines in Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Section 6, pp. 23–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf; native interfaces: https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/PolyTime.lean, definition ComputableInPolyTime; Cslib MultiTapeTM.Configuration at pinned platform revision 254e30e.

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.native_polynomial_simulation :
    (∀ (f : Word → Word),
      Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits →
        ∀ A : Language,FunctionInPWithOracle A f) ∧
    (∀ (f : Word → Bool),
      Turing.MultiTapeTM.ComputableInPolyTime f Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBool →
        ∀ A : Language,InOracleP A (fun x=>f x=true)) := by sorry
