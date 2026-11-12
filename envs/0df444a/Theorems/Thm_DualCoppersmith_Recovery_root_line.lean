-- Prove2me | Theorems.Thm_DualCoppersmith_Recovery_root_line
-- name    : DualCoppersmith.Recovery.root_line
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-10T02:55:33.595713+00:00
-- url     : https://prove2.me/theorems/ce18ba74-d40d-4449-a8e5-01203c5cc965
-- title:
--   Lemma 3.2 — Root line
-- statement:
--   Let $(p,F,X)$ be a bounded modular root instance with arbitrary valid shift parameters $m,t$, and let $r\in\mathbb Z^\ell$ satisfy all strict box bounds and original congruences. Write $n=|T_t|$, $\rho=\operatorname{lcm}_{\alpha\in T_t}X^\alpha$, and $v_r=((\rho/X^\alpha)r^\alpha)_\alpha$. Then all three assertions hold:
--
--   $$v_r\in L_X^\perp,\qquad L_X^\perp\cap\mathbb Rv_r=\mathbb Zv_r,\qquad \|v_r\|\le\rho\sqrt n.$$
--
--   The equality concerns intersection with the entire real line, including all irrational real multiples as candidates. It states primitivity in the constructed lattice, not in the ambient integer lattice. This lemma supplies the complete root-line interface for recovery.
--
--   **Formalization Note** Norms are Euclidean and scalings are exact positive integer quotients.
--
--   Differences from the source:
--   - encoding: one-based variables and a fixed ordered monomial set → zero-based finite indices and a fixed equivalence enumerating all multi-indices of total degree at most t; reason: reindexing preserves every coordinate and uses the Euclidean norm
--   - encoding: degree is defined for nonzero polynomials although zero input relations are not excluded → zero relations have total degree zero and identically zero shift rows are omitted; reason: such rows impose only 0 = 0; every nonzero shift and every input instance is retained
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 8, Lemma 3.2 (PDF p. 9)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Lattice

set_option autoImplicit false

namespace DualCoppersmith.Recovery

/-- Lemma 3.2, printed p. 8 / PDF p. 9: all three clauses. -/
theorem root_line (I : Instance) (P : Parameters I) (r : Fin I.ell → ℤ)
    (hr : IsBoundedRoot I r) :
    rootVector I P r ∈ scaledLattice I P ∧
    ((scaledLattice I P : Set (LLLFactor.RedBasis.Vec (dimension I P))) ∩
      Set.range (fun c : ℝ => c • rootVector I P r) =
      Set.range (fun c : ℤ => c • rootVector I P r)) ∧
    ‖rootVector I P r‖ ≤ (rho I P : ℝ) * Real.sqrt (dimension I P : ℝ) := by sorry

end DualCoppersmith.Recovery
