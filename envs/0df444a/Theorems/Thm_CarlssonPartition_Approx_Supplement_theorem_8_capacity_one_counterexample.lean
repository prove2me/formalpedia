-- Prove2me | Theorems.Thm_CarlssonPartition_Approx_Supplement_theorem_8_capacity_one_counterexample
-- name    : CarlssonPartition.Approx.Supplement.theorem_8_capacity_one_counterexample
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T21:34:16.269151+00:00
-- url     : https://prove2.me/theorems/8b314b6e-948a-40aa-95e0-fb7c7bfba4db
-- title:
--   Theorem 8, p. 14 (corrected: refutation at capacity q = 1) — the printed leading term vanishes
-- statement:
--   Theorem 8 as printed cannot hold on its stated capacity domain. At capacity $q=1$, for any geometric constant $\beta$, any real value $J$ of the geometric integral, any fleet size $m$, any speed $v$, any real workload function $W(\lambda)$, and any real delivery-time function $T(\lambda)$,
--    $$
--    L(\lambda)=\frac{\beta^2\lambda(1-1/q)^2J^2}{2m^2v^2(1-W(\lambda))^2}=0.
--    $$
--    Consequently, along every nontrivial filter $F$,
--    $$
--    \neg\left(\frac{T(\lambda)}{L(\lambda)}\longrightarrow1\right).
--    $$
--    In Lean the ratio is identically zero; in ordinary asymptotic notation an equivalence to the identically zero leading term is not a defined ratio assertion. This obstruction applies to every proposed routing-policy witness, without assuming the desired optimality, existence or unbiasedness. It refutes the printed full-domain existence-and-performance conjunction; the corrected positive statement (capacity at least two, Poisson arrivals, finite spatial second moment) is the separate item `theorem_8`.
--
--    **Formalization Note** A separate verification file proves this negation without importing any open theorem and instantiates a nontrivial one-sided filter. The source allows $q=1$ on p.6, prints this coefficient on p.14 and divides by $1-1/q$ in its ec11 proof. No capacity restriction has been inserted to hide the excluded case.
--
--   Differences from the source:
--   - correction: Theorem 8 asserts a spatially unbiased policy with its displayed ratio limit for every positive integer capacity, including q=1. → At q=1 no real delivery-time function has that ratio limit along any nontrivial filter.; reason: The exact factor (1-1/q)^2 is zero, so the entire normalized ratio is identically zero; this is a counterexample to the printed claim at q=1; the corrected q>=2 statement is the separate item theorem_8.
--   - encoding: The numerator contains the geometric integral of the square root of f and the denominator contains the heterogeneous workload. → The integral is the real parameter J, the workload is a function load, and the filter is any NeBot real filter.; reason: The obstruction holds for every choice of these objects, including each source instance and its nontrivial heavy-traffic filter; no stochastic performance premise is needed.
-- source:
--   Carlsson, Liu, Salari and Yu, Provably Good Region Partitioning for On-Time Last-Mile Delivery, accepted manuscript (SSRN 3915544; published in Operations Research 72(1):91–109, 2024, doi:10.1287/opre.2021.0588), p. 14 (PDF 15), Theorem 8; capacity domain p. 6 (PDF 7); proof p. ec11 (PDF 48)

import Mathlib

namespace CarlssonPartition.Approx.Supplement

open Filter

/-- Counterexample to Theorem 8 as printed on its full capacity domain: for `q = 1`
no real delivery-time function can have the required ratio limit along a nontrivial
filter. `J` stands for the source's integral of the square root of the density;
`load` stands for its heterogeneous workload. The obstruction is independent of
these values and therefore applies to every admissible routing-policy witness. -/
theorem theorem_8_capacity_one_counterexample
    (q : ℕ) (hq : q = 1) (beta J v : ℝ) (m : ℕ)
    (load T : ℝ → ℝ) (F : Filter ℝ) [NeBot F] :
    ¬ Tendsto (fun lam => T lam /
      (beta ^ 2 * lam * (1 - 1 / (q : ℝ)) ^ 2 * J ^ 2 /
        (2 * (m : ℝ) ^ 2 * v ^ 2 * (1 - load lam) ^ 2))) F (nhds 1) := by sorry

end CarlssonPartition.Approx.Supplement
