-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_circuit_dense_reduction
-- name    : ApproxPolySatCH.Main.circuit_dense_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T16:12:45.967126+00:00
-- url     : https://prove2.me/theorems/e1ba0901-db74-4e27-9bdc-5914131a183f
-- title:
--   Proposition 6 — Circuit to dense APS
-- statement:
--   Let $k=\mathbb Q$ or any finite coefficient field with its specified representation. The division-free shared-DAG version of approximate polynomial satisfiability has a deterministic polynomial-time many-one reduction to the dense-array version:
--   $$\mathrm{APS}^{\mathrm{circuit}}_k\le_m^P\mathrm{APS}^{\mathrm{dense}}_k.$$
--   The function is computed by a finite machine with one polynomial bit-time bound valid on all words. Validity and exact image-closure semantics are included in the two languages; empty, zero and constant systems are covered.
--
--   This preserves the source's circuit-input interpretation of the main theorem.
--
--   Differences from the source:
--   - encoding: Division-free circuits and dense polynomial inputs over a fixed coefficient field. → Languages of finite shared DAGs and complete total-degree coefficient arrays with explicit binary scalar and wire codes.; reason: The tagged representations preserve the source inputs; invalid codes are no instances and negative constants implement subtraction.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Proposition 6, p.14 (PDF p.14); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=14

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

theorem circuit_dense_reduction (k : CoefficientField) :
    ManyOneReduction (CircuitLanguage k) (DenseLanguage k) := by sorry

end ApproxPolySatCH.Main
