-- Prove2me | Theorems.Thm_FamousTheorems_orzech_theorem
-- name    : FamousTheorems.orzech_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:12.449716+00:00
-- url     : https://prove2.me/theorems/b5e1564d-8363-491d-a834-f9f9fc8a9360
-- title:
--   Orzech's theorem
-- statement:
--   **Orzech's theorem.** Let $R$ be a ring, $M$ a Noetherian $R$-module and $N$ an $R$-module. If $i:N\to M$ is injective and $f:N\to M$ is surjective, then $f$ is injective.
--
--   The case $N=M$, $i=\mathrm{id}$ is Vasconcelos's theorem that a surjective endomorphism of a Noetherian module is an isomorphism. Orzech's result says more generally that a Noetherian module has no submodule mapping onto it with a nontrivial kernel.
--
--   **Formalization note.** Mathlib's `IsNoetherian.injective_of_surjective_of_injective`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsNoetherian.injective_of_surjective_of_injective`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem orzech_theorem {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [IsNoetherian R M]
    (i f : N →ₗ[R] M) (hi : Function.Injective i) (hf : Function.Surjective f) : Function.Injective f := by sorry

end FamousTheorems
