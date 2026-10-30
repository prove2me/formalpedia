-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_entropy_derivative
-- name    : BramsonQueueing.FIFOKelly.entropy_derivative
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:07:40.503239+00:00
-- url     : https://prove2.me/theorems/3ea20f67-6aa6-41f0-bab5-9ee5f28105bc
-- title:
--   Proposition 5.12 — FIFO Kelly entropy derivative identity
-- statement:
--   For any FIFO fluid solution $X=(A,D,T,W,Y,Z)$ of Kelly type, let $h(x)=x\log x$, $h_k(x)=x\log(x/\lambda_k)$ and let $H$ be the integrated departure entropy (5.24). At every regular time $t$ the asserted derivative is
--   $$H'(t)=\sum_k[h_k(A_k'(t))-h_k(D_k'(t))]-\sum_j\frac{1}{m_j^s}h(1+W_j'(t)).$$
--   Here $m_j^s$ is the station service mean. The assertion supplies existence of this derivative as well as its value; regularity requires component derivatives, not global continuous differentiability. No subcriticality or positive-reference-rate assumption is inserted. This is the identity used in the dissipation bounds.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - reading: h_k(x)=x log(x/lambda_k), with no convention when lambda_k=0 → the displayed real expression uses 1/0=0 and log(0)=0, so h_k(x)=0 at zero reference rate; reason: the brief prescribes this definite full-domain reading; no positive-rate hypothesis or corrected theorem replaces the printed target
--   - encoding: derivatives at regular nonnegative times → derivatives within the nonnegative half-line, with a right derivative at zero; reason: only the domain on which the source paths are defined is used
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Proposition 5.12, printed [150], PDF [158]

import Definitions.Def_BramsonQueueing_FIFOKelly_Entropy

namespace BramsonQueueing.FIFOKelly

theorem entropy_derivative {K J : ℕ} (p : Parameters K J)
    (hk : KellyType p) (X : SixPaths K J) (hX : (fifoModel p).Solution X) :
    ∀ t, Regular X t → HasDerivWithinAt (entropy p X)
      (entropyFlux p X t - stationEntropyFlux p X t) (Set.Ici 0) t := by sorry

end BramsonQueueing.FIFOKelly
