-- Prove2me | Theorems.Thm_ConsistentSubmodular_CompatibleProfile_checkpoint_of_finite_checkpoint
-- name    : ConsistentSubmodular.CompatibleProfile.checkpoint_of_finite_checkpoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:43.6267+00:00
-- url     : https://prove2.me/theorems/a07790b7-7840-4bb5-b0aa-5fad3c644a82
-- title:
--   Common checkpoint for compatible profiles from the finite checkpoint statement
-- statement:
--   Let $P$ be a compatible profile on types $0,\dots,m$ with residuals $r_t(i)$ and objectives $f_t$, and assume
--
--   * $r_0(0)=1$ and $r_t(i)\le r_t(t)$ for all $t,i$;
--   * (the finite checkpoint statement) for all $m',N\in\mathbb{N}$ and every canonical atomic profile $Q$ with stages $0,\dots,m'$ and $N$ atoms, there are a point $p$ and polygonal paths `entry`, `exit` such that $p$ lies in the simplex, has support size at most $2$, satisfies $\tfrac34 B_t\le Q.\mathrm{value}_t(p)$ for all $t$, `entry` runs from vertex $0$ to $p$ and is safe at stage $0$ at level $\tfrac34$, `exit` runs from $p$ to vertex $m'$ and is safe at stage $m'$ at level $\tfrac34B_{m'}$, and `entry.pieces`$+$`exit.pieces` $\le (m'+1)+2$.
--
--   Then there exist a point $p$ and polygonal paths `entry`, `exit` such that:
--
--   1. $p$ is in the simplex and has at most two nonzero coordinates;
--   2. for every $t\in\{0,\dots,m\}$: $\ \tfrac34\,f_t(\{t\})\le F_t(p)$, where $F_t(p)$ is the multilinear value (the expectation of $f_t$ under independent type samples with distribution $p$);
--   3. `entry` starts at vertex $0$ and ends at $p$; `exit` starts at $p$ and ends at vertex $m$;
--   4. `entry` is safe at stage $0$ at level $\tfrac34 f_0(\{0\})$, and `exit` is safe at stage $m$ at level $\tfrac34 f_m(\{m\})$, where safe means every point of the path is in the simplex and has multilinear value at least the level;
--   5. `entry.pieces` $+$ `exit.pieces` $\le (m+1)+2$.
--
--   The statement transfers the checkpoint property from canonical atomic profiles to compatible profiles, with the checkpoint, endpoints, safety and affine-piece budget preserved.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/CompletionReduction.lean#L93-L118 (`ConsistentSubmodular.CompatibleProfile.checkpoint_of_finite_checkpoint`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_CompatibleProfiles
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.CompatibleProfile
variable {m : ℕ} (P : CompatibleProfile (m + 1))
variable (hinit : P.residual 0 0 = 1)
variable (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t)
include hinit hopt

theorem ConsistentSubmodular.CompatibleProfile.checkpoint_of_finite_checkpoint (hfinite : FiniteCheckpointGoal) :
    ∃ (p : Point m) (entry exit : PolygonalPath m),
      IsSimplex p ∧ supportCard p ≤ 2 ∧
      (∀ t : Fin (m + 1), (3 : ℝ) / 4 * (P.objective t.val).value {t} ≤ P.multilinearValue t.val p) ∧
      entry.node 0 = vertex 0 ∧
      entry.node (Fin.last entry.pieces) = p ∧
      exit.node 0 = p ∧
      exit.node (Fin.last exit.pieces) = vertex (Fin.last m) ∧
      P.SafePath 0 ((3 : ℝ) / 4 * (P.objective 0).value {0}) entry ∧
      P.SafePath m ((3 : ℝ) / 4 * (P.objective m).value {Fin.last m}) exit ∧
      entry.pieces + exit.pieces ≤ (m + 1) + 2 := by sorry
