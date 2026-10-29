-- Prove2me | Theorems.Thm_BramsonQueueing_FIFOKelly_entropy_nonnegative
-- name    : BramsonQueueing.FIFOKelly.entropy_nonnegative
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:07:42.151983+00:00
-- url     : https://prove2.me/theorems/73f58f37-cc2a-4016-9a67-73aaee517f1a
-- title:
--   Lemma 5.11 — nonnegativity of FIFO Kelly entropy
-- statement:
--   Let $X=(A,D,T,W,Y,Z)$ be any FIFO fluid solution of Kelly type. Write $m_j^s$ for the common service mean at station $j$, $\lambda$ for the total arrival vector, and $H(t)=\sum_k\int_t^{t+W_{s(k)}(t)}h_k(D_k'(r))\,dr$, where $h_k(x)=x\log(x/\lambda_k)$. If every load satisfies $\rho_j\le1$, then
--   $$H(t)\ge0\qquad(t\ge0).$$
--   This is the printed nonnegativity target on its full domain, including zero reference rates. The source finding is recorded separately.
--
--   Differences from the source:
--   - encoding: finitely many classes and stations, with nonnegative real time → Fin K and Fin J, real functions restricted to nonnegative time; reason: finite index relabelling and time representation preserve every source instance
--   - reading: h_k(x)=x log(x/lambda_k), with no convention when lambda_k=0 → the displayed real expression uses 1/0=0 and log(0)=0, so h_k(x)=0 at zero reference rate; reason: the brief prescribes this definite full-domain reading; no positive-rate hypothesis or corrected theorem replaces the printed target
--   - encoding: derivatives at regular nonnegative times → derivatives within the nonnegative half-line, with a right derivative at zero; reason: only the domain on which the source paths are defined is used
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9, Lemma 5.11, printed [149], PDF [157]

import Definitions.Def_BramsonQueueing_FIFOKelly_Entropy

namespace BramsonQueueing.FIFOKelly

theorem entropy_nonnegative {K J : ℕ} (p : Parameters K J)
    (hk : KellyType p) (hr : ∀ j, load p j ≤ 1)
    (X : SixPaths K J) (hX : (fifoModel p).Solution X) :
    ∀ t, 0 ≤ t → 0 ≤ entropy p X t := by sorry

end BramsonQueueing.FIFOKelly
