-- Prove2me | Theorems.Thm_DepthOptQC_Synth_Supplement_theorem_14
-- name    : DepthOptQC.Synth.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:52:09.805178+00:00
-- url     : https://prove2.me/theorems/537eada0-48fb-4347-9249-b8508dc8785a
-- title:
--   Theorem 14 — bounded-arity real decision simulation
-- statement:
--   Uniform constants $K>0$ and $k\in\mathbb N$ work for both QUNC and its Fan-Out variant QUNCf. If $C$ is a depth-$d$ circuit and $s\ge2$ bounds its gate count and width, then for every $\varepsilon\in(0,1/2)$ there is a QRNC circuit $\widetilde C$—or QRNCf in the Fan-Out case—such that
--   $$|p_{\widetilde C}(x)-p_C(x)|\le\varepsilon$$
--   for every input $x$. Its depth is at most
--   $$K\bigl(d+1+\log_2\log_2(s/\varepsilon)\bigr),$$
--   and its size is at most $K(s+\log_2(2/\varepsilon))^k$.
--
--   In contrast to Theorem 12, the size is polynomial in $\log(1/\varepsilon)$ rather than in $1/\varepsilon$.
--
--   Differences from the source:
--   - reading: $O(d+\log\log(s/\varepsilon))$ and $\operatorname{poly}(s,\log(1/\varepsilon))$ → uniform witnesses $K,k$, using the positive scales $1+\log_2\log_2(s/\varepsilon)$ and $\log_2(2/\varepsilon)$; reason: explicit uniform asymptotics without weakening the precision dependence
--   - encoding: two separately stated model pairs → one Boolean index selecting QUNC/QRNC or QUNCf/QRNCf; reason: retains both clauses exactly
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, Theorem 14, p.65 (PDF p.67), Eq. (313)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

namespace DepthOptQC.Synth.Supplement

open QAlgorithms

/-- **Theorem 14 (Bounded-Arity Real Decision Simulation)** — Vasconcelos,
arXiv:2609.34659, p.65, Eq. (313). QUNC decision circuits have QRNC simulations with additive
`O(log log(s/ε))` depth and size polynomial in `s` and `log(1/ε)`; the same holds for the Fan-Out
pair QUNCf/QRNCf.

**Formalization Note.** The Boolean `withFanout` states both source clauses without dropping either.
`precLog ε=log₂(2/ε)` and `loglogScale` give positive uniform representatives of the two printed
asymptotic logarithms. -/
theorem theorem_14 :
    ∃ K : ℝ, 0 < K ∧ ∃ k : ℕ,
      ∀ (withFanout : Bool) (n d s : ℕ)
        (C : DecisionCircuit (if withFanout then quncfGateSet else quncGateSet) n),
        2 ≤ s → C.depth = d → C.size ≤ s → C.width ≤ s →
        ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
          ∃ Ctilde : DecisionCircuit (if withFanout then qrncfGateSet else qrncGateSet) n,
            (Ctilde.depth : ℝ) ≤
              K * ((d : ℝ) + loglogScale ((s : ℝ) / ε)) ∧
            (Ctilde.size : ℝ) ≤ K * ((s : ℝ) + DepthOptQC.Synth.precLog ε) ^ k ∧
            ∀ x : Qubits n, |Ctilde.acceptance x - C.acceptance x| ≤ ε := by sorry

end DepthOptQC.Synth.Supplement
