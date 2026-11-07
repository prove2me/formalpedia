-- Prove2me | Theorems.Thm_CtxSearchTSR_section_2_2_posDef_preserved
-- name    : CtxSearchTSR.section_2_2_posDef_preserved
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:00.730596+00:00
-- url     : https://prove2.me/theorems/df426c7c-703f-42dd-b221-7baaeca57b5a
-- title:
--   §2.2, p.10 — the updates (10) preserve $R_t\succ0$ (Algorithm 2 is well defined)
-- statement:
--   Algorithm 2 is well defined: its scale matrix stays positive definite.
--
--   1. If $R\succ0$, then for every context $x$ and every $\varepsilon,Y\in\{-1,1\}$ the updated matrix $R+\frac{\varepsilon Y}{a(3-\varepsilon Y)}uu^\top$ of (10) (with $u=Rx$, $a=x^\top u$) is positive definite.
--   2. For every target $z$, every adaptive context strategy, every sequence of learner signs and every round $t$, the scale matrix $R_t$ of Algorithm 2 is positive definite.
--
--   The case $\varepsilon Y=1$ adds a positive semidefinite matrix; the case $\varepsilon Y=-1$ is Remark 2.3.
--
--   **Formalization Note** At $x=0$ the update is the identity (Lean's $c/0=0$). At $d=0$ every matrix is (vacuously) positive definite.
--
--   Differences from the source:
--   - encoding: the update (10) at a context x (a = 0 when x = 0, where (10) is undefined) → x = 0 allowed; the update is then the identity by Lean's c/0 = 0; reason: the paper: for x_t = 0 nothing changes (App. C.3, p.21)
--   - generalization: the scale matrices of Algorithm 2 for ‖z‖₂ ≤ 1 and contexts with ‖x_t‖₂ ≤ 1 → every target z, every context strategy (no norm bound) and every sign sequence; reason: the property never uses the norm bounds; it specializes to the paper's runs
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.2, paragraph before Remark 2.3 and the remark's last sentence, p.10

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **R_t ≻ 0 for every round of Algorithm 2.** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…),
§2.2, p.10 (the paragraph before Remark 2.3, and the last sentence of the remark).

"We first verify that the algorithm is well-defined, meaning that the updates in (10) preserve the
positive definiteness of the scale matrix R_t ≻ 0."

1. One step: if R ≻ 0 then, for every context x and every e, Y ∈ {−1, 1}, the updated matrix of
   (10) is positive definite.
2. The run: for every target, every context strategy, every sign sequence and every round t, the
   scale matrix of Algorithm 2 is positive definite.

**Formalization Note.** x = 0 is allowed: then u = 0, a = 0, and Lean's `/ 0 = 0` makes the update
the identity. At d = 0 every matrix on `Fin 0` is positive definite. -/
theorem section_2_2_posDef_preserved {d : ℕ} :
    (∀ (s : State d) (x : Fin d → ℝ) (e Y : ℝ), s.R.PosDef → (e = 1 ∨ e = -1) →
      (Y = 1 ∨ Y = -1) → (update s x e Y).R.PosDef) ∧
    (∀ (z : Fin d → ℝ) (X : ContextStrategy d) (ε : ℕ → Bool) (t : ℕ),
      (run z X ε t).R.PosDef) := by sorry

end CtxSearchTSR
