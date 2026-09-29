-- Prove2me | Theorems.Thm_AlgebraicClosure_exists_cycloChar_family
-- name    : AlgebraicClosure.exists_cycloChar_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/8cca03bf-d9b9-5b8d-8e3f-989f70cab16e
-- title:
--   Existence of a mod q cyclotomic character family
-- statement:
--   The assertion is the existence of a family, indexed by the natural numbers $q$, of group homomorphisms $\mathrm{cyc}_q \colon \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to (\mathbb{Z}/q\mathbb{Z})^{\times}$, where $\overline{\mathbb{Q}}$ is Mathlib's algebraic closure of $\mathbb{Q}$ and the automorphism group is that of $\mathbb{Q}$-algebra isomorphisms of $\overline{\mathbb{Q}}$ with itself, with the following property: for every prime $q$, every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and every $\mu \in \overline{\mathbb{Q}}$ satisfying $\mu^{q} = 1$, one has $\sigma(\mu) = \mu^{n}$, where $n$ is the canonical representative in $\{0,\dots,q-1\}$ of the residue class underlying the unit $\mathrm{cyc}_q(\sigma) \in (\mathbb{Z}/q\mathbb{Z})^{\times}$ (the `val` of its image in $\mathbb{Z}/q\mathbb{Z}$). Note the shape: the homomorphism is produced for every natural number $q$, but the compatibility with the action on $q$-th roots of unity is required only at primes $q$; at composite $q$ and at $q = 0$ nothing is asserted about the value of $\mathrm{cyc}_q$. No uniqueness is claimed.
--
--   This is the mod $q$ cyclotomic character of the absolute Galois group of $\mathbb{Q}$, packaged as a single family over all $q$ so that it can be fed to a binder expecting such a family. It is used in the assembly of patching data in the modularity-lifting arguments, for instance by [`CuspForm.heckeLocal.exists_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_of_not_cube_dvd_of_level_not_cube_dvd`](thm.html#CuspForm.heckeLocal.exists_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_of_not_cube_dvd_of_level_not_cube_dvd) and the related existence and presentation results for the local Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicClosure_exists_cycloChar_family.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicClosure.exists_cycloChar_family :
    ∃ cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ),
      ∀ q : ℕ, q.Prime → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
        μ ^ q = 1 → σ μ = μ ^ ((cyc q σ : ZMod q).val) := by sorry
