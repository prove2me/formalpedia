-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_closure_eq_derived_cuts
-- name    : CombOpt.ChvatalRank.closure_eq_derived_cuts
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:08:33.325978+00:00
-- url     : https://prove2.me/theorems/a5632677-9cd7-46f4-baac-43fc7f65a743
-- title:
--   §6.7, p. 230 — $P'$ is the same with cuts from valid inequalities and cuts derived from $Ax\le b$
-- statement:
--   Let $P=\{x : Ax\le b\}$. The closure $P'$, defined with the cuts $c^Tx\le\lfloor d\rfloor$ obtained from valid inequalities $c^Tx\le d$ for $P$, equals the set of vectors of $P$ that satisfy every cut
--   $$
--   (y^TA)x\le\lfloor y^Tb\rfloor,\qquad y\ge0,\quad y^TA\text{ integral},
--   $$
--   derived from the system.
--
--   This connects the geometric closure with the derivations used in cutting-plane proofs, and it is the form of $P'$ the proof of Theorem 6.34 starts from.
--
--   Differences from the source:
--   - reading: Gomory-Chvátal cutting planes "can also be defined directly" from valid inequalities → the two families of cuts define the same closure; reason: as families of inequalities they differ by dominated cuts: for P = {0} in ℝ¹ with rows x ≤ 0, −x ≤ 0, the cut 0x ≤ 5 comes from a valid inequality but is not derived from the system; the closures, and so everything the book does with them, agree
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §6.7, p. 230 (PDF 238), and the proof of Theorem 6.34, p. 233 (PDF 241)

import Mathlib
import Definitions.Def_RobustToDynamics_polyhedron
import Definitions.Def_CombOpt_ChvatalRank_chvatalClosure
import Definitions.Def_CombOpt_ChvatalRank_IsDerivedCut

open Matrix

namespace CombOpt.ChvatalRank

/-- **The two definitions of a cut agree on the closure.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §6.7, p. 230 (PDF 238): "Gomory-Chvátal
cutting planes can also be defined directly in terms of the polyhedron P defined by (6.20)". The
points of `P = {x : Ax ≤ b}` satisfying all cuts `(6.21)` derived from the system are exactly `P′`.

**Formalization Note.** For any real system. The multipliers `y` range over all nonnegative reals. -/
theorem closure_eq_derived_cuts {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    chvatalClosure (RobustToDynamics.polyhedron A b) =
      {x | x ∈ RobustToDynamics.polyhedron A b ∧
        ∀ (y : Fin m → ℝ) (c : Fin n → ℝ) (t : ℝ),
          IsDerivedCut (fun i => A i) b y c t → c ⬝ᵥ x ≤ t} := by sorry

end CombOpt.ChvatalRank
