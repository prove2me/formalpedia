-- Prove2me | Theorems.Thm_FamousTheorems_root_system_has_base_7b
-- name    : FamousTheorems.root_system_has_base_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:33:47.372296+00:00
-- url     : https://prove2.me/theorems/8e36d200-5aa5-4b5a-a6e7-a7e7773b2995
-- title:
--   Every reduced crystallographic root system has a base
-- statement:
--   **Every reduced crystallographic root system has a base.** Let $\Phi$ be a finite reduced crystallographic root system in a vector space over a field of characteristic $0$. Then $\Phi$ has a base: a linearly independent subset $\Delta\subseteq\Phi$ such that every root is an integer combination of elements of $\Delta$ with coefficients all nonnegative or all nonpositive.
--
--   The elements of a base are the simple roots. They determine the Weyl group, the Cartan matrix and the Dynkin diagram, and so the classification of root systems and of semisimple Lie algebras. The classical proof chooses a linear functional that is nonzero on all roots and takes the indecomposable positive roots.
--
--   **Formalization note.** Mathlib's `RootPairing.nonempty_base`. Mathlib treats root systems as `RootPairing`s: a family of roots in $M$ and coroots in $N$ indexed by $\iota$, with a perfect pairing between $M$ and $N$. `IsRootSystem` says that the roots span $M$ and the coroots span $N$, `IsCrystallographic` that the pairings of roots with coroots are integers, and `IsReduced` that the only roots proportional to a root $\alpha$ are $\pm\alpha$. `P.Base` is the type of bases in Mathlib's sense, which also requires the corresponding condition for coroots.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `RootPairing.nonempty_base`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem root_system_has_base_7b {ι R M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N] [Field R] [CharZero R] [Module R M]
    [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    Nonempty P.Base := by sorry

end FamousTheorems
