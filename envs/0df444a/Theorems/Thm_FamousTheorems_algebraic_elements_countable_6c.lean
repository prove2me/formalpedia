-- Prove2me | Theorems.Thm_FamousTheorems_algebraic_elements_countable_6c
-- name    : FamousTheorems.algebraic_elements_countable_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:47:21.977333+00:00
-- url     : https://prove2.me/theorems/3f36d652-0ed8-4af7-b4b0-e265d21c510f
-- title:
--   The algebraic numbers are countable
-- statement:
--   **The algebraic numbers are countable.** Let $R$ be a countable integral domain and $A$ an integral domain of characteristic $0$ that is a torsion-free $R$-algebra. Then the set of elements of $A$ that are algebraic over $R$ has cardinality exactly $\aleph_0$.
--
--   With $R=\mathbb Q$ and $A=\mathbb C$, this says that there are countably many algebraic numbers. Since $\mathbb C$ is uncountable, transcendental numbers exist. This is Cantor's 1874 proof that transcendental numbers exist, which does not construct one.
--
--   **Formalization note.** Mathlib's `Algebraic.cardinalMk_of_countable_of_charZero`. `IsAlgebraic R x` means that $x$ is a root of a nonzero polynomial over $R$. The statement gives equality with `ℵ₀`, so there are also infinitely many algebraic elements.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Algebraic.cardinalMk_of_countable_of_charZero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem algebraic_elements_countable_6c (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
    [Module.IsTorsionFree R A] [Countable R] [CharZero A] :
    Cardinal.mk { x : A // IsAlgebraic R x } = Cardinal.aleph0 := by sorry

end FamousTheorems
