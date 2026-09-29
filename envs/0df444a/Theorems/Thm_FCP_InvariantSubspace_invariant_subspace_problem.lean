-- Prove2me | Theorems.Thm_FCP_InvariantSubspace_invariant_subspace_problem
-- name    : FCP.InvariantSubspace.invariant_subspace_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:51:52.300976+00:00
-- url     : https://prove2.me/theorems/94bd6447-676b-4674-9820-812c2a071fe9
-- title:
--   Invariant subspace problem for separable Hilbert spaces
-- statement:
--   **The invariant subspace problem.** Does every bounded linear operator $T$ on a separable complex Hilbert space $H$ of dimension at least $2$ have a nontrivial closed invariant subspace, i.e. a closed subspace $W$ with $\{0\} \ne W \ne H$ and $T(W) \subseteq W$? The statement is recorded here in the affirmative. The dimension hypothesis is needed because in dimension $\le 1$ every subspace is $\{0\}$ or $H$. Counterexamples are known on other Banach spaces (Enflo; Read on $\ell^1$), and the Hilbert space case remains open.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean); https://en.wikipedia.org/wiki/Invariant_subspace_problem

import Mathlib
import Definitions.Def_FCP_InvariantSubspace

namespace FCP.InvariantSubspace

theorem invariant_subspace_problem (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [TopologicalSpace.SeparableSpace H] [CompleteSpace H] (hdim : 2 ≤ Module.rank ℂ H)
    (T : H →L[ℂ] H) : Nonempty (ClosedInvariantSubspace T) := by sorry

end FCP.InvariantSubspace
