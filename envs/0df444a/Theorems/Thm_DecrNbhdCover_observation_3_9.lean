-- Prove2me | Theorems.Thm_DecrNbhdCover_observation_3_9
-- name    : DecrNbhdCover.observation_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:05:33.395566+00:00
-- url     : https://prove2.me/theorems/a33dbe14-ba12-490f-b230-d01045763be7
-- title:
--   Observation 3.9 — partial and proper path-transforming emulators are monotone in $D$
-- statement:
--   Let $G$ be a decremental graph and $0<\epsilon<1$, $0<d\le D\le D'$. If $H$ is a partial $(\epsilon,d,D)$-emulator for $G$, then it is a partial $(\epsilon,d,D')$-emulator for $G$. Similarly, if $H$ is a proper path-transforming $(\epsilon,d,D)$-emulator for $G$, then it is a proper path-transforming $(\epsilon,d,D')$-emulator for $G$.
--
--   This lets the construction use one emulator at all larger scales.
--
--   Differences from the source:
--   - reading: "every path $P$" in Property Q1 → every simple path; reason: $P[v,a]$ and "$a\in V(P)\setminus\{v\}$" are used for simple paths: the proof in C.2 takes "the vertex that lies furthest from $v$ on $P$", and on a walk returning to $v$ its choice of $a$ can equal $v$
--   - reading: the algorithm is "deterministic", and no machine is named → one program of the published word RAM `DynConnWC.Program` with no `rand` instruction, at unit cost per instruction; reason: a running time needs a machine, and the paper counts ordinary word operations
--   - encoding: "path-transforming" as the existence of an algorithm → a named program $Q$ with constants $C,c_0$ reading the history of $G$ and $H$, kept in the conclusion; reason: for one fixed finite history the existence alone would be empty; the named form implies the existential one
--   - encoding: abstract graphs and updates → vertices $0,\dots,n-1$, edges numbered by input order, and supernodes and edges of a well-structured graph numbered in order of insertion, all given as words; reason: a machine reads words; relabeling changes no instance
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Observation 3.9, p.19 (PDF 23)

import Mathlib
import Definitions.Def_DecrNbhdCover_MaintainEmulator

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-- **Observation 3.9.** Chuzhoy, Mosenzon, *A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems* (STOC 2027 submission, sha256 4278ef58…), p.19 (PDF 23).

"Let G be a decremental graph and let 0 < ϵ < 1 and 0 < d ≤ D ≤ D′ be parameters. Assume that H is a partial (ϵ, d, D)-emulator for G. Then H is a partial (ϵ, d, D′)-emulator for G. Similarly, if H is a proper path-transforming (ϵ, d, D)-emulator for G, then it is a proper path-transforming (ϵ, d, D′)-emulator for G."

**Formalization Note.** The second clause is stated for a history of `G` and `H` given by update streams, with the transforming program `Q` kept. -/
theorem observation_3_9 (eps : ℝ) (d : ℕ) (D D' : ℝ) (heps : 0 < eps) (heps1 : eps < 1) (hd : 0 < d)
    (hdD : (d : ℝ) ≤ D) (hDD' : D ≤ D') :
    (∀ {α β ε η : Type} (G : ℕ → Graph α ε) (H : ℕ → WSGraph α β η),
      IsPartialDyn G H eps d D → IsPartialDyn G H eps d D') ∧
    (∀ (Q : Program) (C c₀ : ℕ) (A : EmuHistory),
      IsProperPT Q C c₀ A eps d D → IsProperPT Q C c₀ A eps d D') := by sorry

end DecrNbhdCover
