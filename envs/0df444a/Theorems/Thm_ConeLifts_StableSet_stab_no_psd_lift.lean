-- Prove2me | Theorems.Thm_ConeLifts_StableSet_stab_no_psd_lift
-- name    : ConeLifts.StableSet.stab_no_psd_lift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:20:55.812921+00:00
-- url     : https://prove2.me/theorems/71b010c6-65f2-4bb1-83d5-28913d6e7259
-- title:
--   Theorem 5.2 — $\mathrm{STAB}(G)$ of a graph on $n \ge 1$ vertices has no $\mathcal S^n_+$-lift
-- statement:
--   Let $G$ be any graph with $n \ge 1$ vertices. Then the stable set polytope $\mathrm{STAB}(G) \subseteq \mathbb R^n$ does not admit an $\mathcal S^n_+$-lift: there is no affine subspace $L$ of the real $n\times n$ matrices and no linear map $\pi$ into $\mathbb R^n$ with
--
--   $$
--   \mathrm{STAB}(G) = \pi(\mathcal S^n_+ \cap L).
--   $$
--
--   For a perfect graph $G$, Lovász's construction gives an $\mathcal S^{n+1}_+$-lift of $\mathrm{STAB}(G)$ (Theorem 5.1); this theorem shows that the matrix size $n+1$ cannot be lowered to $n$, for any graph.
--
--   **Formalization Note** All lifts are excluded, proper or not. The ambient space of the lift is all real $n\times n$ matrices; this does not change which sets have lifts (see `HasPSDLift`). The hypothesis $n \ge 1$ makes explicit that the graph has vertices: for $n = 0$, $\mathrm{STAB}(G) = \{0\} = \pi(\mathcal S^0_+)$ and the printed statement would be false.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, p. 19, Theorem 5.2

import Mathlib
import Definitions.Def_ConeLifts_StableSet_stab
import Definitions.Def_ConeLifts_StableSet_HasPSDLift

namespace ConeLifts.StableSet

/-- **Theorem 5.2** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 19): let `G` be any graph
with `n` vertices. Then `STAB(G)` does not admit a `Sⁿ₊`-lift.

All lifts are excluded, proper or not: there is no affine subspace `L` of the real `n × n`
matrices and no linear map `π` to `ℝⁿ` with `STAB(G) = π(Sⁿ₊ ∩ L)`. The hypothesis `n ≥ 1` is
the paper's reading of "a graph with n vertices": for `n = 0`, `STAB(G) = {0} = π(S⁰₊)` and the
printed statement fails. -/
theorem stab_no_psd_lift (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    ¬ HasPSDLift n (stab G) := by sorry

end ConeLifts.StableSet
