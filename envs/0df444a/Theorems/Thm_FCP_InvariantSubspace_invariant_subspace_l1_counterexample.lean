-- Prove2me | Theorems.Thm_FCP_InvariantSubspace_invariant_subspace_l1_counterexample
-- name    : FCP.InvariantSubspace.invariant_subspace_l1_counterexample
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:52:19.382288+00:00
-- url     : https://prove2.me/theorems/69d85cf8-a921-42c8-a803-23a8785c0a44
-- title:
--   Read's operator on $\ell^1$ without invariant subspaces
-- statement:
--   **Read's theorem (1985).** There is a bounded linear operator on $\ell^1(\mathbb{N}; \mathbb{C})$ with no nontrivial closed invariant subspace. Together with Enflo's earlier Banach space example, this shows the invariant subspace problem has a negative answer outside Hilbert spaces, and explains why the Hilbert case needs geometry rather than soft arguments.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/InvariantSubspaceProblem.lean); C. J. Read, A solution to the invariant subspace problem on the space $\ell_1$, Bull. London Math. Soc. 17 (1985), 305--317

import Mathlib
import Definitions.Def_FCP_InvariantSubspace

namespace FCP.InvariantSubspace

theorem invariant_subspace_l1_counterexample :
    ∃ T : (lp (fun _ : ℕ => ℂ) 1) →L[ℂ] (lp (fun _ : ℕ => ℂ) 1),
      IsEmpty (ClosedInvariantSubspace T) := by sorry

end FCP.InvariantSubspace
