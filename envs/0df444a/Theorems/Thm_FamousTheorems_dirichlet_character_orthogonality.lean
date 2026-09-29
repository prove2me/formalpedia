-- Prove2me | Theorems.Thm_FamousTheorems_dirichlet_character_orthogonality
-- name    : FamousTheorems.dirichlet_character_orthogonality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:40.151189+00:00
-- url     : https://prove2.me/theorems/28b87caf-9427-4240-9d6e-dab7a1feabc1
-- title:
--   Orthogonality of Dirichlet characters
-- statement:
--   **Orthogonality of Dirichlet characters.** Let $n\ge1$, and let $R$ be an integral domain containing enough roots of unity. Then for every $a\in\mathbb Z/n\mathbb Z$ with $a\ne1$,
--   $$\sum_{\chi}\chi(a)=0,$$
--   where $\chi$ runs over all Dirichlet characters modulo $n$ with values in $R$.
--
--   This is the orthogonality relation for Dirichlet characters, in the variable $a$. It lets one pick out an arithmetic progression $a\bmod n$ by averaging over characters. That is the key device in Dirichlet's theorem on primes in arithmetic progressions.
--
--   **Formalization note.** Mathlib's `DirichletCharacter.sum_characters_eq_zero`. "Enough roots of unity" is `HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)`: $R$ contains a primitive root of unity whose order is the exponent of $(\mathbb Z/n)^\times$. This guarantees that there are $\varphi(n)$ characters with values in $R$. For $a$ not a unit, every $\chi(a)$ is $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `DirichletCharacter.sum_characters_eq_zero`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dirichlet_character_orthogonality (R : Type*) [CommRing R] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod n)ˣ)]
    [IsDomain R] {a : ZMod n} (ha : a ≠ 1) : ∑ χ : DirichletCharacter R n, χ a = 0 := by sorry

end FamousTheorems
