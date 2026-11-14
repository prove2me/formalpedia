-- Prove2me | Theorems.Thm_ConsistentSubmodular_CompatibleProfile_checkpoint_zero_scale
-- name    : ConsistentSubmodular.CompatibleProfile.checkpoint_zero_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:35.974139+00:00
-- url     : https://prove2.me/theorems/711166ab-2fc9-4e03-b479-b55d8ce89e5c
-- title:
--   Common checkpoint for compatible profiles at zero scale
-- statement:
--   Let $Q$ be a compatible profile on types $0,\dots,m$, with objectives $f_t$ and residuals $r_t(i)$, such that $r_0(0)=0$ and $r_0(i)\le r_0(0)$ for all $i$ (so all stage-$0$ residuals vanish). Then there exist a point $p$ and polygonal paths `entry`, `exit` such that:
--
--   1. $p$ is in the simplex and has at most two nonzero coordinates;
--   2. for every $t\in\{0,\dots,m\}$: $\ \tfrac34\,f_t(\{t\})\le F_t(p)$, with $F_t$ the multilinear value (expectation of $f_t$ under independent type samples with distribution $p$);
--   3. `entry` starts at vertex $0$ and ends at $p$; `exit` starts at $p$ and ends at vertex $m$;
--   4. `entry` is safe at stage $0$ at level $\tfrac34 f_0(\{0\})$, and `exit` is safe at stage $m$ at level $\tfrac34 f_m(\{m\})$ (every point is in the simplex with multilinear value at least the level);
--   5. `entry.pieces` $+$ `exit.pieces` $\le (m+1)+2$.
--
--   This is the degenerate zero-scale case of the checkpoint reduction: a common exact checkpoint and one direct exit exist without any normalization, atomization or finite-checkpoint assumption.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/CompletionScaling.lean#L138-L176 (`ConsistentSubmodular.CompatibleProfile.checkpoint_zero_scale`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {d : ℕ} (P : CompatibleProfile d)
variable {m : ℕ} (Q : CompatibleProfile (m + 1))

theorem ConsistentSubmodular.CompatibleProfile.checkpoint_zero_scale (hzero : Q.residual 0 0 = 0)
    (hopt0 : ∀ i, Q.residual 0 i ≤ Q.residual 0 0) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (Q.objective t.val).value {t} ≤ Q.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      Q.SafePath 0 ((3 : ℝ) / 4 * (Q.objective 0).value {0}) entry ∧
      Q.SafePath m ((3 : ℝ) / 4 * (Q.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by sorry
