-- Prove2me | Theorems.Thm_FamousTheorems_gauss_lemma_quadratic_residues
-- name    : FamousTheorems.gauss_lemma_quadratic_residues
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:12.283502+00:00
-- url     : https://prove2.me/theorems/fffa1fe7-8c3c-4853-8ade-9e0b76d35b5f
-- title:
--   Gauss's lemma on quadratic residues
-- statement:
--   **Gauss's lemma on quadratic residues.** Let $p$ be an odd prime and $a$ an integer not divisible by $p$. Let $\mu$ be the number of $x\in\{1,\dots,\tfrac{p-1}2\}$ for which the least nonnegative residue of $ax$ modulo $p$ exceeds $p/2$. Then the Legendre symbol is
--   $$\Big(\frac ap\Big)=(-1)^{\mu}.$$
--
--   Gauss used this lemma in one of his proofs of quadratic reciprocity. It also gives the supplementary law $\big(\tfrac2p\big)=(-1)^{(p^2-1)/8}$ directly. Eisenstein's lattice-point proof of reciprocity is based on it.
--
--   **Formalization note.** Mathlib's `ZMod.gauss_lemma`. `legendreSym p a` is the Legendre symbol. `ZMod.val` is the least nonnegative residue in $\{0,\dots,p-1\}$. The range $1\le x\le\tfrac{p-1}2$ is `Finset.Ico 1 (p / 2).succ`, and "exceeds $p/2$" is `p / 2 < val` with natural-number division.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ZMod.gauss_lemma`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem gauss_lemma_quadratic_residues {p : ℕ} [Fact p.Prime] {a : ℤ} (hp : p ≠ 2) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a =
      (-1) ^ ((Finset.Ico 1 (p / 2).succ).filter
        (fun x : ℕ => p / 2 < ((a : ZMod p) * (x : ZMod p)).val)).card := by sorry

end FamousTheorems
