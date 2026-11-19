-- Prove2me | Theorems.Thm_APSCounting893_Main_native_modular_jacobian_verification
-- name    : APSCounting893.Main.native_modular_jacobian_verification
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T19:16:06.18255+00:00
-- url     : https://prove2.me/theorems/22c80eba-653e-4081-84e0-e8bc0c4e3b22
-- title:
--   Polynomial-time modular Jacobian inverse verification
-- statement:
--   For every modulus $p\ge2$, evaluate the row-cleared Jacobian matrix $A$ of a rational arithmetic circuit at a sparse integer assignment, with chosen output and variable indices. A supplied finite list encodes the entries of a matrix $B$ in row order. The executable verification procedure satisfies
--
--   $$\operatorname{Verify}(A,B)=\mathrm{true}\quad\Longleftrightarrow\quad AB=I\ \text{over }\mathbb Z/p\mathbb Z.$$
--
--   The verifier is computed by one finite deterministic binary multitape Turing machine in polynomial time in the complete encoded input length. The polynomial bounds both time and space uniformly over every circuit, modulus, assignment, index list and proposed inverse, including malformed values outside the algebraic promises. The semantic identity uses the actual integer-polynomial numerator–denominator pairs and their formal derivatives. No determinant expansion is part of the algorithm.
--
--   This result provides a uniform finite certificate checker for the nonzero-minor condition in the image-dimension procedure.
-- source:
--   Executable modular implementation of Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, p. 23, Lemma 6.1 and equation (6.1), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf#page=23. Native machine semantics and binary arithmetic: https://github.com/cslib-community/complexitylib/tree/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape. The modular witness reduction is APSCounting893.Main.bounded_modular_dimension_certificates.

import Definitions.Def_APSCounting893_Main_ModularJacobianComputation
import Definitions.Def_APSCounting893_Main_ModularJacobianData
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open APSCounting893.Main

theorem APSCounting893.Main.native_modular_jacobian_verification :
    Turing.MultiTapeTM.ComputableInPolyTime
      (fun q : MatrixParameters × List ℕ => residueMatrixInverseTest q.1 q.2)
      (Turing.MultiTapeTM.encPair encMatrixParameters (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encNat))
      Turing.MultiTapeTM.encBool ∧
    (∀ (n k p : ℕ) (hp : 2 ≤ p) (C : ArithmeticCircuit n) (a : List (Fin n × ℤ))
      (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) (inverse : List ℕ),
      residueMatrixInverseTest
        (p,(C.raw,(rawAssignmentOf a,(List.ofFn (fun i => (o i).val),List.ofFn (fun j => (v j).val)))))
        inverse = true ↔
      (clearedIntegerMatrix (circuitJacobianIntegerPairs C o v)).map
        (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun l => (sparseAssignmentPoint a l : ZMod p)))*
        Matrix.of (fun i j : Fin k => (inverse.getD (i.val*k+j.val) 0 : ZMod p))=1) := by sorry
