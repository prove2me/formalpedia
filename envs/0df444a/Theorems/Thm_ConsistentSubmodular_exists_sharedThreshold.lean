-- Prove2me | Theorems.Thm_ConsistentSubmodular_exists_sharedThreshold
-- name    : ConsistentSubmodular.exists_sharedThreshold
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:52.67576+00:00
-- url     : https://prove2.me/theorems/ad14d80f-a6b7-4983-8a0c-b043f71bec46
-- title:
--   Existence of a shared-threshold coupling for any vector of probabilities
-- statement:
--   Let $d\in\mathbb N$ and let $z=(z_t)_{t<d}$ with $0\le z_t\le 1$ for every $t$. Then a shared-threshold coupling for $z$ exists. Such a coupling consists of a finite probability space (a finite number of cells with a probability law) together with a map assigning to each cell $\omega$ an active set $\mathrm{active}(\omega)\subseteq\{0,\dots,d-1\}$ such that
--
--   1. each $t$ is active with probability exactly $z_t$, and
--   2. the active sets are monotone in $z$: if $z_s\le z_t$ and $s\in\mathrm{active}(\omega)$, then $t\in\mathrm{active}(\omega)$.
--
--   This is the standard single-uniform-threshold coupling of Bernoulli variables with different parameters. In the reduction it allows the independent samples attached to different type vectors to be coupled so that the expected number of changed coordinates between two samples is the type $\ell_1$ distance.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SharedThreshold.lean#L47-L82 (`ConsistentSubmodular.exists_sharedThreshold`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.exists_sharedThreshold {d : ℕ} (z : Fin d → ℝ) (hz : ∀ t, 0 ≤ z t ∧ z t ≤ 1) :
    Nonempty (SharedThreshold z) := by sorry
