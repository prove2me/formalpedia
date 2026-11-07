-- Prove2me | Theorems.Thm_CFLOutliers_theorem_1_1
-- name    : CFLOutliers.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:38:49.807975+00:00
-- url     : https://prove2.me/theorems/6f823ae5-34aa-40af-91ea-9e8e53f0f822
-- title:
--   Theorem 1.1 — a deterministic polynomial-time $(60/11+\varepsilon)$-approximation for capacitated facility location with outliers
-- statement:
--   For every $0<\varepsilon\le 1$, metric capacitated facility location with outliers admits a deterministic $(60/11+\varepsilon)$-approximation, with running time polynomial in the binary input length and $1/\varepsilon$, for explicitly represented unit-demand clients.
--
--   Precisely: there are one Turing machine $\mathcal M$ and one constant $c$ such that for every well-formed rational instance $I$ that has a capacity-feasible solution serving at least $q$ clients, and every rational $0<\varepsilon\le 1$, the machine, started on the encoding of $(I,\varepsilon)$ (of length $N$), halts within
--
--   $$c\,\bigl(N+\lceil 1/\varepsilon\rceil+2\bigr)^c$$
--
--   steps with the encoding of a solution $S$ that
--
--   1. respects every hard capacity,
--   2. serves at least $q$ clients, and
--   3. satisfies $c(S)\le(60/11+\varepsilon)\,\mathrm{OPT}$.
--
--   Opening costs are arbitrary and capacities nonuniform. The earlier exact-feasible guarantees for this problem required uniform opening costs.
--
--   Differences from the source:
--   - reading: "deterministic … The running time is polynomial in the binary input length and 1/ε" → one Mathlib TM2 machine M and one constant c, chosen before the instance and ε, halting with the encoded output within c·(N + ⌈1/ε⌉ + 2)^c steps on the encoded (I, ε), N the input length; reason: the paper names no machine model; a deterministic polynomial-time algorithm in any standard model is simulated by a Turing machine with polynomial overhead
--   - reading: ε a real number with 0 < ε ≤ 1 → ε a rational number with 0 < ε ≤ 1, read from the input; reason: the algorithm uses ε to compute τ, η and K of (21), so it is an input; every real ε ∈ (0, 1] has a rational ε′ ∈ [ε/2, ε], so no case is lost
--   - reading: "(60/11 + ε)-approximation" → the guarantee is required on every instance with a capacity-feasible solution serving at least q clients; other inputs may receive any output; reason: OPT is undefined on an infeasible instance
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - encoding: facilities, clients, solutions, the binary input → Fin m, Fin n, an open Finset with an Option-valued assignment; a fixed binary encoding (encGoalIn, encSol) with the full (m + n) × (m + n) distance matrix; inputs that are not well formed may receive any output; reason: Lean convention; the same instances
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Theorem 1.1, p.2

import Mathlib
import Definitions.Def_CFLOutliers_OPT
import Definitions.Def_CFLOutliers_encInst
import Definitions.Def_CFLOutliers_OutputsWithin

namespace CFLOutliers

open OnlineCRS.Combine (Sym)

/-- **Theorem 1.1** (Dabas, arXiv:2611.04094, p.2): "For every 0 < ε ≤ 1, metric capacitated
facility location with outliers admits a deterministic (60/11 + ε)-approximation. The running
time is polynomial in the binary input length and 1/ε, for explicitly represented unit-demand
clients."

There are one Turing machine and one constant `c` such that, for every well-formed rational
instance with a feasible solution and every rational `0 < ε ≤ 1`, the machine, given the encoded
instance and `ε` (input length `N`), outputs within `c (N + ⌈1/ε⌉ + 2)^c` steps an encoded
solution that is capacity-feasible, serves at least `q` clients, and costs at most
`(60/11 + ε) OPT`.

**Formalization Note.** The machine is Mathlib's deterministic `Turing.TM2ComputableAux` over
`Sym = Fin 4`; inputs are binary (`encGoalIn`), outputs `encSol`. Distances form a rational
pseudometric on `F ⊔ C`. Inputs that are malformed or infeasible may receive any output. -/
theorem theorem_1_1 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
      ∀ (I : RInst), I.WellFormed → I.toInst.Feasible →
      ∀ ε : ℚ, 0 < ε → ε ≤ 1 →
        ∃ S : Sol I.toInst,
          S.CapFeasible ∧ I.toInst.q ≤ (served S).card ∧
          cost S ≤ (60 / 11 + (ε : ℝ)) * OPT I.toInst ∧
          OutputsWithin M (encGoalIn I ε) (encSol S)
            (c * ((encGoalIn I ε).length + ⌈ε⁻¹⌉₊ + 2) ^ c) := by sorry

end CFLOutliers
