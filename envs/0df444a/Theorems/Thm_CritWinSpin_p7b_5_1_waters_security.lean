-- Prove2me | Theorems.Thm_CritWinSpin_p7b_5_1_waters_security
-- name    : CritWinSpin.p7b_5_1_waters_security
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:48:15.515069+00:00
-- url     : https://prove2.me/theorems/679ade56-d0bf-4d97-9465-db792fb55373
-- title:
--   Existential unforgeability for recoverable Waters circuit records
-- statement:
--   There is a universal constant $C>0$ for the following reduction. Let a Waters verification circuit have polynomial-time public evaluation and signature-recovery maps, preserve the message bits, and be injective on honest message/randomness pairs. Suppose also that honest generation induces exactly the uniform law $V_P$ on its valid-record set $\Omega_P$.
--
--   For every PPT algorithm $A$ and every efficiently computable polynomial sample bound $T(d)\ge1$, there is a PPT algorithm $B$ such that, for all sufficiently large $d$,
--   $$
--   \Pr\!\left[A(P,F_{1:T})=F_*\in\Omega_P,\
--   \Psi_P(F_*)\notin\{\Psi_P(F_t)\}_{t=1}^{T}\right]
--   \le C\,T(d)\sqrt d\,\operatorname{Adv}_{\mathrm{CDH}}(B;d).
--   $$
--   The probability is over key generation, $T$ independent records from $V_P$, and the coins of $A$. No CDH hardness assumption is needed: this is the algorithmic reduction itself. Effective recovery converts a fresh valid record into a fresh Waters message–signature pair.
-- source:
--   Liu–Zhang–Ren, The Critical Window for Sampling and Learning-to-Sample in Spin Systems, STOC 2027 submission #943 (manuscript sha256 f77584da…), Theorem 5.1(iii), eq. (27), printed pp.19–21, invoking HJK12 Theorem 2.3 and RV26 Theorem 47.

import Mathlib
import Definitions.Def_CritWinSpin_SourceReduction

open QAlgorithms.Complexity QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

theorem p7b_5_1_waters_security :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : BilinearFamily) (circ : WatersCircuit F),
      SourceCircuitRecords circ →
      (∀ d, 1 ≤ d → ∀ desc, GenSupport F.gen d desc → ∀ (key : WatersKey F desc d)
        (y : BinCfg (circ.n0 d)), circ.genLaw d desc key y = unifOn (circ.omega d desc key) y) →
      SourceSecurity F circ.toSource C := by sorry
