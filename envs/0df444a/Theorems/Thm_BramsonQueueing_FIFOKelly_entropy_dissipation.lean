-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_entropy_dissipation
-- name    : BramsonQueueing.FIFOKelly.entropy_dissipation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:07:38.097359+00:00
-- url     : https://prove2.me/theorems/d929781e-2ff5-424e-b4c8-b90544e11a38
-- title:
--   Proposition 5.13 — all entropy flux and dissipation bounds
-- statement:
--   Fix a FIFO fluid model of Kelly type. With $h,h_k,H,m_j^s$ as in (5.21)–(5.24), there is one $c_6>0$, depending only on the model, such that for every solution and every regular time,
--   $$\sum_k[h_k(A_k')-h_k(D_k')]\le\sum_k Z_k',$$
--   $$\sum_j\frac{h(1+W_j')}{m_j^s}\ge\sum_k Z_k'+c_6\sum_j(W_j')^2,$$
--   $$H'\le-c_6\sum_j(W_j')^2.$$
--   All three clauses (5.35)–(5.37) remain one item. The same constant works for all times and all initial data. Under the disclosed zero-rate reading the recorded two-station example falsifies the first and third clauses; this is a source finding, not a reason to replace the target.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - reading: h_k(x)=x log(x/lambda_k), with no convention when lambda_k=0 → the displayed real expression uses 1/0=0 and log(0)=0, so h_k(x)=0 at zero reference rate; reason: the brief prescribes this definite full-domain reading; no positive-rate hypothesis or corrected theorem replaces the printed target
--   - encoding: derivatives at regular nonnegative times → derivatives within the nonnegative half-line, with a right derivative at zero; reason: only the domain on which the source paths are defined is used
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Proposition 5.13, printed [150, 151], PDF [158, 159]

import Definitions.Def_BramsonQueueing_FIFOKelly_Entropy

namespace BramsonQueueing.FIFOKelly

theorem entropy_dissipation {K J : ℕ} (p : Parameters K J) (hk : KellyType p) :
    ∃ c₆ : ℝ, 0 < c₆ ∧ ∀ X : SixPaths K J, (fifoModel p).Solution X →
      ∀ t, Regular X t →
        entropyFlux p X t ≤ queueDerivative X t ∧
        queueDerivative X t + c₆ * workloadDissipation X t ≤ stationEntropyFlux p X t ∧
        rate (entropy p X) t ≤ -c₆ * workloadDissipation X t := by sorry

end BramsonQueueing.FIFOKelly
