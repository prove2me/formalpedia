-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_halfMixture_certificate
-- name    : ConsistentSubmodular.WindowInstance.halfMixture_certificate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:33.692553+00:00
-- url     : https://prove2.me/theorems/89d8dba3-13a7-4030-8e20-7e29793e0d3f
-- title:
--   Theorem B.4 — half-mixture certificate with three segments
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, objective $f$, benchmarks $P_j=f(O_j\cup R_j)$, credits $K_j=2(P_j-f(R_j))-\bigl(f(R_j\cup O_0)-f(R_j)\bigr)$, and envelope $D_\beta=\max_j\bigl(2K_j-4(1-\beta)P_j\bigr)$. Let $\tfrac12\le\beta\le\tfrac34$ and $\alpha\le\beta$ with $2\beta\alpha\le1$. Let $c$ be a stage with $D_\beta\le K_c$ and $K_j<D_\beta$ for every $j>c$ (the last eligible partner). Then there is an $(\alpha,3)$-certificate $Z$ for $W$ whose anchor is the half mixture
--   $$\text{anchor}(Z)=\tfrac12\,\delta_0+\tfrac12\,\delta_c ,$$
--   whose entry path has exactly one segment and whose exit path has exactly two segments.
--
--   Here an $(\alpha,3)$-certificate consists of a simplex point (the anchor) with $\alpha P_j\le H_j(\text{anchor})$ at all stages $j$, an entry path in the simplex from $\delta_0$ to the anchor on which $H_0\ge\alpha P_0$, an exit path in the simplex from the anchor to $\delta_m$ on which $H_m\ge\alpha P_m$, and at most $3$ segments in total; $H_j$ is the mixture value of stage $j$.
--
--   This is the main certificate construction of Section 3 for the range $\beta\in[\tfrac12,\tfrac34]$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean#L278-L395 (`ConsistentSubmodular.WindowInstance.halfMixture_certificate`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.halfMixture_certificate {α β : ℝ} (hβ : 1 / 2 ≤ β) (hβ' : β ≤ 3 / 4)
    (hαβ : α ≤ β) (hα : 2 * β * α ≤ 1) {c : Fin (W.lastStage + 1)}
    (hDc : W.envelope β ≤ W.credit c) (hafter : ∀ j, c < j → W.credit j < W.envelope β) :
    ∃ Z : W.Certificate α 3, Z.anchor = mix (vertex 0) (vertex c) (1 / 2) ∧
      Z.entry.pieces = 1 ∧ Z.exit.pieces = 2 := by sorry
