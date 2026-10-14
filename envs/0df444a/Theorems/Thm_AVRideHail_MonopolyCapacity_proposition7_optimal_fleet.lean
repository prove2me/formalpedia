-- Prove2me | Theorems.Thm_AVRideHail_MonopolyCapacity_proposition7_optimal_fleet
-- name    : AVRideHail.MonopolyCapacity.proposition7_optimal_fleet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:10:19.227884+00:00
-- url     : https://prove2.me/theorems/e7afeff1-142c-4731-842a-2644274918e6
-- title:
--   Proposition 7, p. 28 — given capacity N, the optimal AV fleet in a scenario is min{N, n*_{HV,i}}
-- statement:
--   Consider a common-platform market with $a > 0$, $0 < r < 1$, $t_2 > 0$, $V > 0$, constant HV reservation earnings $w_0$ ($\alpha = 0$), and AV costs $c_v, c_f > 0$ with $c_v + c_f < w_0$ (Assumption 1). Fix a scenario with potential demand mass $m > 0$, a loose market (condition (33)), maximal stable pure-HV equilibrium demand $d^*$, and $n^*_{HV} = \underline{n}(d^*)$. Given an AV capacity $N \ge 0$, the monopoly supplier chooses its fleet $n_{AV} \in [0, N]$ to maximize its total variable profit $\pi^C(n_{AV})\, n_{AV}$, where $\pi^C$ is the per-AV profit (251). Then
--   $$n_{AV} = \min\{N, n^*_{HV}\}$$
--   is the unique maximizer: if $N < n^*_{HV}$ the supplier deploys its whole capacity, and if $N \ge n^*_{HV}$ it deploys exactly $n^*_{HV}$ AVs, the supply level that keeps HVs out of the market.
--
--   This solves the second stage of the monopoly's two-stage problem (5); the first-stage capacity choice is Proposition 8.
--
--   **Formalization Note.** The proposition's closing sentence (total fleet size and price equal those of the pure-HV market) is the content of Proposition 6, which the mission takes as the definition (251) of $\pi^C$; it is not restated. The case "$(n^*_{HV} - N)$ HVs join the market" is likewise part of Proposition 6's equilibrium and not restated.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), p. 28, Proposition 7; proof App. E.1.2, pp. 84–85

import Mathlib
import Definitions.Def_AVRideHail_MonopolyCapacity_Model

namespace AVRideHail.MonopolyCapacity

theorem proposition7_optimal_fleet (P : AVRideHail.PureHV.MarketParams) (ha : 0 < P.a) (hr0 : 0 < P.r)
    (hr1 : P.r < 1) (ht2 : 0 < P.t2) (hV : 0 < P.V) (halpha : P.alpha = 0)
    (cv cf : ℝ) (hcv : 0 < cv) (hcf : 0 < cf) (hA1 : cv + cf < P.w0)
    (m : ℝ) (hm : 0 < m) (hloose : AVRideHail.PureHV.LooseMarket P m)
    (dstar : ℝ) (hdstar : AVRideHail.PureHV.IsMaxStableEq P m dstar) (N : ℝ) (hN : 0 ≤ N) :
    IsMaxOn (fun n => piC P cv m dstar n * n) (Set.Icc 0 N) (min N (AVRideHail.PureHV.nMin P dstar)) ∧
      ∀ n ∈ Set.Icc 0 N,
        piC P cv m dstar n * n = piC P cv m dstar (min N (AVRideHail.PureHV.nMin P dstar)) * min N (AVRideHail.PureHV.nMin P dstar) →
          n = min N (AVRideHail.PureHV.nMin P dstar) := by sorry

end AVRideHail.MonopolyCapacity
