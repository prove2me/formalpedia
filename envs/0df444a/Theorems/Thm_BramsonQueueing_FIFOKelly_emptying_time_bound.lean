-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_emptying_time_bound
-- name    : BramsonQueueing.FIFOKelly.emptying_time_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:06:32.261992+00:00
-- url     : https://prove2.me/theorems/8a30206c-dc59-4f15-b3d6-371e47d514a6
-- title:
--   Lemma 5.14 — uniform station emptying-time bound
-- statement:
--   Fix any subcritical network parameters and consider every solution of the six basic fluid equations. This includes the solutions of every fluid model obtained by imposing any auxiliary equations on these parameters. For a solution $X$, write $W^M(t)=\max_jW_j(t)$ and let $\tau_j(t)$ be the additional time until station $j$ is next empty. There is one finite constant $c_2>0$ such that, for every solution, every $t\ge0$ and every station,
--   $$\tau_j(t)\le c_2W^M(t).$$
--   The constant is uniform over initial data, solutions, times and stations. This item is not restricted to FIFO or Kelly type. The incorrect state-dependent coefficient in the printed proof is recorded separately and is not used as the theorem's constant.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - encoding: additional time until the station is next empty → an extended nonnegative infimum, equal to infinity if the station never empties; reason: the finite upper bound retains the emptying assertion instead of using a real infimum with a default zero
--   - encoding: some constant c_2 → a positive real constant c_2; reason: a valid constant can be increased to a positive one because maximum workload is nonnegative
--   - encoding: every subcritical fluid model → all solutions of the subcritical basic model, before any auxiliary equations are imposed; reason: the source includes the basic model; every other model has a subset of its solutions, so the formulations recover each other without restricting disciplines
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Lemma 5.14, printed [152], PDF [160]

import Definitions.Def_BramsonQueueing_FIFOKelly_Fluid

namespace BramsonQueueing.FIFOKelly

theorem emptying_time_bound {K J : ℕ} (p : Parameters K J)
    (hs : Subcritical p) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ X, BasicFluid p X → ∀ t, 0 ≤ t → ∀ j,
      emptyingTime X j t ≤ ENNReal.ofReal (c₂ * maximumWorkload X t) := by sorry

end BramsonQueueing.FIFOKelly
