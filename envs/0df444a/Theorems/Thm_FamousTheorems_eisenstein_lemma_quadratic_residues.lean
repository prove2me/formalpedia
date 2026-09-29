-- Prove2me | Theorems.Thm_FamousTheorems_eisenstein_lemma_quadratic_residues
-- name    : FamousTheorems.eisenstein_lemma_quadratic_residues
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:43.213256+00:00
-- url     : https://prove2.me/theorems/7ac12676-c6e9-4ab8-a15e-0fc65802f13f
-- title:
--   Eisenstein's lemma on quadratic residues
-- statement:
--   **Eisenstein's lemma.** Let $p$ be an odd prime and $a$ an odd natural number not divisible by $p$. Then
--   $$\Big(\frac ap\Big)=(-1)^{\sum_{x=1}^{(p-1)/2}\lfloor xa/p\rfloor},$$
--   where $\big(\frac ap\big)$ is the Legendre symbol.
--
--   Eisenstein used this lattice-point form of Gauss's lemma to give his well-known geometric proof of quadratic reciprocity: for distinct odd primes $p,q$ the two exponents count lattice points under the diagonal of a $\frac{p-1}2\times\frac{q-1}2$ rectangle.
--
--   **Formalization note.** Mathlib's `ZMod.eisenstein_lemma`. The sum runs over `Finset.Ico 1 (p / 2).succ`, i.e. $x=1,\dots,(p-1)/2$, with natural-number floor division `x * a / p`. The condition $p\nmid a$ is `(a : ZMod p) ≠ 0`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.eisenstein_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem eisenstein_lemma_quadratic_residues {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = (-1) ^ ∑ x ∈ Finset.Ico 1 (p / 2).succ, x * a / p := by sorry

end FamousTheorems
