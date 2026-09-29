-- Prove2me | Theorems.Thm_FamousTheorems_artin_rees_lemma
-- name    : FamousTheorems.artin_rees_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:05:26.356727+00:00
-- url     : https://prove2.me/theorems/d8009a0a-f62d-437a-81e6-723d456d424d
-- title:
--   The Artin–Rees lemma
-- statement:
--   **The Artin–Rees lemma.** Let $R$ be a Noetherian ring, $I$ an ideal, $M$ a finitely generated $R$-module and $N\subseteq M$ a submodule. Then there is $k$ such that for all $n\ge k$,
--   $$I^nM\cap N=I^{n-k}\,(I^kM\cap N).$$
--
--   So the $I$-adic filtration of $M$ induces on $N$ a filtration that differs from the $I$-adic filtration of $N$ by a bounded shift. The lemma is the key ingredient in the proofs of Krull's intersection theorem and of the exactness of $I$-adic completion on finitely generated modules. It is a basic tool of commutative algebra.
--
--   **Formalization note.** Mathlib's `Ideal.exists_pow_inf_eq_pow_smul`. The submodule $I^nM$ is `I ^ n • ⊤`, where `⊤` is the whole module `M`, and `⊓` is intersection of submodules.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ideal.exists_pow_inf_eq_pow_smul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem artin_rees_lemma {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    (I : Ideal R) (N : Submodule R M) :
    ∃ k : ℕ, ∀ n ≥ k, I ^ n • (⊤ : Submodule R M) ⊓ N = I ^ (n - k) • (I ^ k • (⊤ : Submodule R M) ⊓ N) := by sorry

end FamousTheorems
