-- Prove2me | Theorems.Thm_FamousTheorems_every_set_in_von_neumann_hierarchy_6c
-- name    : FamousTheorems.every_set_in_von_neumann_hierarchy_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:59.98017+00:00
-- url     : https://prove2.me/theorems/868b8abd-c871-4fa4-b5d1-1946165f50b7
-- title:
--   Every set lies in the von Neumann hierarchy
-- statement:
--   **Every set lies in the von Neumann hierarchy.** For every set $x$ there is an ordinal $\alpha$ with $x\in V_\alpha$, where
--   $$V_\alpha=\bigcup_{\beta<\alpha}\mathcal P(V_\beta).$$
--
--   So the universe of sets is the union $V=\bigcup_\alpha V_\alpha$ of the cumulative hierarchy. The theorem follows from the axiom of foundation, and it is equivalent to it over the other axioms of ZF. It defines the rank of a set and lets one prove statements about all sets by induction on rank.
--
--   **Formalization note.** Mathlib's `ZFSet.exists_mem_vonNeumann`. `ZFSet` is Mathlib's model of ZFC sets, and `ZFSet.vonNeumann o` is $V_o$ for an ordinal $o$ in the same universe.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZFSet.exists_mem_vonNeumann`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem every_set_in_von_neumann_hierarchy_6c (x : ZFSet) : ∃ o : Ordinal, x ∈ ZFSet.vonNeumann o := by sorry

end FamousTheorems
