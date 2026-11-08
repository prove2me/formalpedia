-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_29
-- name    : FairFacilityLoc.proposition_3_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:27.469474+00:00
-- url     : https://prove2.me/theorems/01ae2261-2919-499b-9c25-d20f33f58890
-- title:
--   Proposition 3.29 — the median of a heaviest group has ratio at most 3
-- statement:
--   For sublinear group effects, the coordinate-wise median of the reports of group $G_h$, where $h$ is the smallest index with $A_h=\max_jA_j$, is strategyproof and anonymous, and its ratio is at most $3$ in every dimension.
--
--   This is the ratio bound of Theorem 3.1 for $d\ge4$.
--
--   **Formalization Note** The mechanism is written through the cut rule of §2.2, and the statement has a further clause identifying it with the median: with $k=|G_h|$, the output in coordinate $r$ is a report of a member of $G_h$, at least $\lceil k/2\rceil$ members report at most it, and at least $k-\lceil k/2\rceil+1$ report at least it.
--
--   Differences from the source:
--   - encoding: the coordinate-wise median of the reports of $G_h$ → the cut rule of §2.2 with an added clause identifying the output as the order statistic $v_{\lceil k/2\rceil}$; reason: §2.2 and the proof of Proposition 3.3 show these are the same mechanism; the clause lets a reader check it
--   - encoding: in every dimension → $1\le d$; reason: dimensions are positive throughout the paper
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.29, p.50 (PDF p.52); median clause in the proof of Proposition 3.3, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_FairFacilityLoc_IsStrategyproof
import Definitions.Def_FairFacilityLoc_ratio
import Definitions.Def_FairFacilityLoc_medianMechanism

open scoped ENNReal

namespace FairFacilityLoc

/-- **Proposition 3.29** (Yan, Zhou, manuscript, sha256 642a1268…, p.50, PDF p.52). In every dimension, on sublinear group
effects, the coordinate-wise median of the reports of `G_h`, where `h` is the smallest index with `A_h = max_j A_j`, is
strategyproof and anonymous, and its ratio is at most `3`.

**Formalization Note.** `medianMechanism` is written through the cut rule of §2.2. The first clause identifies it with
the printed median, in the terms of the proof of Proposition 3.3, p.19, PDF p.21: `y_r` is the report of a member of `G_h`,
at least `⌈k/2⌉` members report at most `y_r`, and at least `k − ⌈k/2⌉ + 1` report at least `y_r`, with `k = |G_h|`.
That determines the order statistic `v_{⌈k/2⌉}`. The subtraction is moved to the other side to stay in `ℕ`. -/
theorem proposition_3_29 (d : ℕ) (hd : 1 ≤ d) :
    (∀ {n m : ℕ} (G : GroupStructure n m) (x : Fin n → GeoSemialgCSP.E d) (r : Fin d),
      let Gh := G.G (heaviestGroup G)
      let y := medianMechanism d G x
      (∃ i ∈ Gh, x i r = y r) ∧
        ⌈(Gh.card : ℝ) / 2⌉₊ ≤ (Gh.filter fun i => x i r ≤ y r).card ∧
        Gh.card + 1 ≤ (Gh.filter fun i => y r ≤ x i r).card + ⌈(Gh.card : ℝ) / 2⌉₊) ∧
      IsStrategyproof (medianMechanism d) ∧
      IsAnonymous (medianMechanism d) ∧
      ratio (medianMechanism d) ≤ 3 := by sorry

end FairFacilityLoc
