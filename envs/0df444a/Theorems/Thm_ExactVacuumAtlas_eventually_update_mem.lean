-- Prove2me | Theorems.Thm_ExactVacuumAtlas_eventually_update_mem
-- name    : ExactVacuumAtlas.eventually_update_mem
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-13T10:10:49.521545+00:00
-- url     : https://prove2.me/theorems/1d76c33f-ca15-4864-af08-a8ee0093a0e8
-- title:
--   Coordinate slices through a point of an open set stay in the set nearby
-- statement:
--   Let $n$ be a natural number, $V\subseteq\mathbb R^n$ an open set, $x\in V$ and $i$ a coordinate index. Then for all $u$ in some neighbourhood of $x_i$ the point $x[x_i:=u]$ (the point $x$ with its $i$-th coordinate replaced by $u$) lies in $V$: $$\exists\,\delta>0\ \ \forall u,\ |u-x_i|<\delta\ \Rightarrow\ x[x_i:=u]\in V.$$ (Stated as an eventually-true property in the neighbourhood filter of $x_i$; $n=0$ is allowed and vacuous.)
--
--   Locality lemma: on an open domain, facts about a coordinate slice may be used only near the current coordinate value; it is what lets the certificates transfer differentiability from the domain to each one-variable slice.
--
--   **Formalization Note** Points are functions $\mathrm{Fin}\,n\to\mathbb R$ with the product topology; the conclusion is `∀ᶠ u in 𝓝 (x i), Function.update x i u ∈ V`.
-- source:
--   elementary topology of R^n (standard); Lean source: repository ExactVacuumAtlas (private repository, not publicly accessible; GitHub remote pending (no GitHub identity on the build server)), commit 35f26e6a22f5d72380094fa94edc72dea667df53, Atlas/Core/Pd.lean#L26-L33 (module Atlas.Core.Pd, file sha256 de5add9938c9a8be29fbeea73f501181f6cd5e596029c40b44e10ae21b047ab1; uploaded stub = platform_mirror/Theorems/Thm_ExactVacuumAtlas_eventually_update_mem.lean)

import Mathlib
import Definitions.Def_Atlas_Core_Basic
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.eventually_update_mem {V : Set (Pt n)} (hV : IsOpen V) {x : Pt n} (hx : x ∈ V)
    (i : Fin n) : ∀ᶠ u in 𝓝 (x i), Function.update x i u ∈ V := by sorry
