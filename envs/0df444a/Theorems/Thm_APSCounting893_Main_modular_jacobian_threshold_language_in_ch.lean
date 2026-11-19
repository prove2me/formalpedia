-- Prove2me | Theorems.Thm_APSCounting893_Main_modular_jacobian_threshold_language_in_ch
-- name    : APSCounting893.Main.modular_jacobian_threshold_language_in_ch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:38:55.358487+00:00
-- url     : https://prove2.me/theorems/0ee143bc-6968-4ad5-a68c-2e16012ce614
-- title:
--   Uniform Counting Hierarchy language for modular Jacobian thresholds
-- statement:
--   There is one total language $A$ at one fixed level of the Counting Hierarchy such that, for every valid rational arithmetic circuit $C$ and every nonnegative integer $k$,
--
--   $$A(\langle\operatorname{enc}(C),\operatorname{enc}(k)\rangle)\iff\operatorname{ModJac}(C,k).$$
--
--   Here $\operatorname{ModJac}(C,k)$ is the bounded modular Jacobian certificate predicate: it selects injective output and variable indices, a prime of the stated linear bit-length bound, and a sparsely encoded integer assignment of the stated quadratic length bound, at which the cleared integer Jacobian minor is nonzero modulo that prime. Divisions are interpreted in the circuit's rational-function field before the polynomial-output promise is applied. The variable count and unused variable labels may be given in binary.
--
--   The language and its hierarchy level are fixed before every circuit and every threshold. This is the threshold-decision component of uniform image-dimension computation in Lemma 6.1; answers on words outside the valid circuit encodings are unrestricted.
-- source:
--   Jacobian-rank threshold component of Agarwal, Hari, Pandey, Shukla, STOC 2027 submission #893, Lemma 6.1 and proof, p. 23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_ModularJacobianData
import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.modular_jacobian_threshold_language_in_ch :
    ∃ A : Language,InCountingHierarchy A ∧
      ∀ (n : ℕ) (C : ArithmeticCircuit n),ValidCircuit .rational C →
        ∀ k : ℕ,A (pairWord C.encode (encodeNat k)) ↔ ModularJacobianCertificate C k := by sorry
