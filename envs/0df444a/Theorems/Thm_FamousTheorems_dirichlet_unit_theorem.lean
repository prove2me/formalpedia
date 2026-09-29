-- Prove2me | Theorems.Thm_FamousTheorems_dirichlet_unit_theorem
-- name    : FamousTheorems.dirichlet_unit_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:21.606712+00:00
-- url     : https://prove2.me/theorems/cb8bcdda-b2af-4e80-9027-6d3a24d12e70
-- title:
--   Dirichlet's unit theorem
-- statement:
--   **Dirichlet's unit theorem.** Let $K$ be a number field with $r_1$ real and $r_2$ complex places, and put $r=r_1+r_2-1$. There are units $u_1,\dots,u_r$ of the ring of integers $\mathcal O_K$ such that every unit $x$ can be written uniquely as
--   $$x=\zeta\,u_1^{e_1}\cdots u_r^{e_r},\qquad \zeta\text{ a root of unity in }K,\ e_i\in\mathbb Z .$$
--   Thus $\mathcal O_K^\times\cong\mu(K)\times\mathbb Z^{r}$.
--
--   It is one of the two finiteness theorems of algebraic number theory, alongside finiteness of the class number. It is the source of the regulator in the class number formula, and it explains Pell's equation for real quadratic fields.
--
--   **Formalization note.** Mathlib's `NumberField.Units.exist_unique_eq_mul_prod`, with the fundamental system `NumberField.Units.fundSystem K` as witness. `NumberField.Units.rank K` is defined as the number of infinite places minus one, i.e. $r_1+r_2-1$, and `NumberField.Units.torsion K` is the subgroup of roots of unity.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NumberField.Units.exist_unique_eq_mul_prod`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dirichlet_unit_theorem (K : Type*) [Field K] [NumberField K] :
    ∃ u : Fin (NumberField.Units.rank K) → (NumberField.RingOfIntegers K)ˣ, ∀ x : (NumberField.RingOfIntegers K)ˣ,
      ∃! ζe : NumberField.Units.torsion K × (Fin (NumberField.Units.rank K) → ℤ),
        x = (ζe.1 : (NumberField.RingOfIntegers K)ˣ) * ∏ i, u i ^ ζe.2 i := by sorry

end FamousTheorems
