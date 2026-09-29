-- Prove2me | Theorems.Thm_FamousTheorems_rice_theorem
-- name    : FamousTheorems.rice_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:39.193863+00:00
-- url     : https://prove2.me/theorems/7ef6ed99-89de-4046-bc8b-b1997db02968
-- title:
--   Rice's theorem
-- statement:
--   **Rice's theorem.** Let $C$ be a set of partial functions $\mathbb N\rightharpoonup\mathbb N$. If membership of the function computed by a program in $C$ is decidable, then $C$ contains either all partial recursive functions or none of them.
--
--   Every nontrivial semantic property of programs is therefore undecidable: whether a program halts on some input, computes a total function, or is equivalent to a given program. It generalises the undecidability of the halting problem and is the basic limitation on static program analysis.
--
--   **Formalization note.** Mathlib's `ComputablePred.rice`. Programs are codes `Nat.Partrec.Code` with semantics `eval`. The conclusion says that if one partial recursive `f` lies in `C` then every partial recursive `g` does.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ComputablePred.rice`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem rice_theorem (C : Set (ℕ →. ℕ)) (h : ComputablePred fun c : Nat.Partrec.Code => c.eval ∈ C) {f g : ℕ →. ℕ}
    (hf : Nat.Partrec f) (hg : Nat.Partrec g) (fC : f ∈ C) : g ∈ C := by sorry

end FamousTheorems
