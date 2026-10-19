-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_max_identity
-- name    : CarlssonPartition.Approx.max_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:04:21.443361+00:00
-- url     : https://prove2.me/theorems/d0e46721-fc6c-4225-80f3-4d3ccf3584a4
-- title:
--   Proof of Proposition 3, ec13 — algebraic maximum equals 4η/(1−η)²
-- statement:
--   For a real error factor $0\le\eta<1$, the larger of the relative upper and lower deviations is the upper deviation, and it simplifies to
--   $$
--   \max\left\{\left(\frac{1+\eta}{1-\eta}\right)^2-1,\;
--   1-\left(\frac{1-\eta}{1+\eta}\right)^2\right\}
--   =\left(\frac{1+\eta}{1-\eta}\right)^2-1
--   =\frac{4\eta}{(1-\eta)^2}.
--   $$
--   This real algebra identity converts the two district comparisons into the paper's absolute error factor.
--
--   **Formalization Note** The hypothesis $0\le\eta<1$ is the sign range used in the Proposition 3 proof; this item states only the algebraic part of its last display.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), proof of Proposition 3, p. ec13 (PDF 50), final display

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Setting

namespace CarlssonPartition.Approx

theorem max_identity (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1) :
    max (((1 + η) / (1 - η)) ^ 2 - 1)
        (1 - ((1 - η) / (1 + η)) ^ 2) =
      ((1 + η) / (1 - η)) ^ 2 - 1 ∧
    ((1 + η) / (1 - η)) ^ 2 - 1 = 4 * η / (1 - η) ^ 2 := by sorry
end CarlssonPartition.Approx
