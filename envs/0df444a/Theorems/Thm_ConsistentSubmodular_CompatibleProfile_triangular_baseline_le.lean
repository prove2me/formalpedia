-- Prove2me | Theorems.Thm_ConsistentSubmodular_CompatibleProfile_triangular_baseline_le
-- name    : ConsistentSubmodular.CompatibleProfile.triangular_baseline_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:04.749452+00:00
-- url     : https://prove2.me/theorems/5c51489a-1da2-4e14-b20a-728dceb841e2
-- title:
--   Baseline bound for the triangular lengths of a compatible profile
-- statement:
--   Let $P$ be a compatible profile on the types $0,\dots,m$: objectives $f_t$ ($t\in\mathbb{N}$) whose values increase and whose marginals decrease with $t$, with baseline $L_t=f_t(\emptyset)$, residuals $r_t(i)=f_t(\{i\})-L_t$, and losses $\lambda_t(i)=r_t(i)-r_{t+1}(i)$. Define raw lengths $\ell^{\rm raw}(i,j)=r_m(i)$ if $j=m$ and $\ell^{\rm raw}(i,j)=\lambda_j(i)$ otherwise, and triangular lengths $\ell(i,j)=\ell^{\rm raw}(i,j)$ if $i\le j$ and $0$ otherwise. Then for every stage $t\in\{0,\dots,m\}$,
--   $$\sum_{j<t}\ \max_{0\le i\le m}\ \ell(i,j)\;\le\;L_t .$$
--
--   The inner maximum is a finite maximum over all types $i$ (all terms are nonnegative).
--
--   This says that the total column maxima before stage $t$ are paid for by the baseline, which is needed to turn a compatible profile into a triangular array and then an atomic profile (Appendix B).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Triangularization.lean#L163-L177 (`ConsistentSubmodular.CompatibleProfile.triangular_baseline_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Triangularization

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {m : ℕ} (P : CompatibleProfile (m + 1))

theorem ConsistentSubmodular.CompatibleProfile.triangular_baseline_le (t : Fin (m + 1)) :
    (∑ j, if j < t then finiteMaximum Finset.univ (fun i => P.triangularLength i j) else 0) ≤
      P.baseline t.val := by sorry
