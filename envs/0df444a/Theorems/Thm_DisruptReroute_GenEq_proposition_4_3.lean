-- Prove2me | Theorems.Thm_DisruptReroute_GenEq_proposition_4_3
-- name    : DisruptReroute.GenEq.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T04:31:37.418223+00:00
-- url     : https://prove2.me/theorems/87d817e4-561b-433a-aa15-5ce7b5f39d4e
-- title:
--   Proposition 4.3, p. 24 — unique general supply chain network equilibrium
-- statement:
--   Consider a supply chain network satisfying the standing assumptions of §§2–4. Suppose Assumptions 4.1 and 4.2 hold for every order profile the default cascade can produce. Then there is exactly one quadruple of rerouting prices $\Pi$, switching costs $K$, undelivered orders $\Gamma$, and unserved demands $\Delta$ that is a general supply chain network equilibrium:
--
--   $$\exists!\,(\Pi,K,\Gamma,\Delta)\;\operatorname{GeneralEquilibrium}(\Pi,K,\Gamma,\Delta).$$
--
--   Here each secondary and sourcing market satisfies its efficient-allocation and unilateral best-response conditions, while $(\Gamma,\Delta)$ is both the limit of the default cascade begun at zero and a fixed point of its update. The result makes the prices and default cascade determined by the network and the realized production costs.
--
--   **Formalization Note** The firm and good types are nonempty finite sets with zero-based indices. The realization $c_i$ is fixed in the network. Assumption 2.1 is applied over suppliers, and inverse supply is nonnegative on the feasible range. The marginal conditions are quantified over every binary $0/o^m_{ij}$ profile that the cascade can reach. Off-market prices follow p. 23, avoiding artificial nonuniqueness.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), p. 24 (PDF p. 24), Proposition 4.3; proof E-Companion, EC pp. 12–13 (PDF pp. 54–55)

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_Model

namespace DisruptReroute.GenEq

/-- Proposition 4.3: existence and uniqueness of the full equilibrium,
    including every market's prices and the two default profiles. -/
theorem proposition_4_3 {N M : ℕ} (net : Network N M)
    (h : Standing net)
    (hMR : ∀ Γ : Matrix N M, Admissible net Γ →
      ∀ m : Fin M, MarginalRevenue net m (rbar Γ m))
    (hMC : ∀ Δ : Matrix N M, Admissible net Δ →
      ∀ m : Fin M, MarginalCost net m (sbar net Δ m)) :
    ∃! q : Profile N M × Profile N M × Matrix N M × Matrix N M,
      IsGeneralEquilibrium net q.1 q.2.1 q.2.2.1 q.2.2.2 := by sorry

end DisruptReroute.GenEq
