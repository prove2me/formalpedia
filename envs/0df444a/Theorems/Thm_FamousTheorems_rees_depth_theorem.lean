-- Prove2me | Theorems.Thm_FamousTheorems_rees_depth_theorem
-- name    : FamousTheorems.rees_depth_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:02.608058+00:00
-- url     : https://prove2.me/theorems/a7af04b5-cf5d-4db1-b273-f5cd28cd1eb3
-- title:
--   The Rees theorem on depth
-- statement:
--   **The Rees theorem on depth.** Let $R$ be a Noetherian ring, $I$ an ideal, $M$ a finitely generated $R$-module with $IM\ne M$, and $n\in\mathbb N$. The following are equivalent:
--   1. $\operatorname{Ext}^i_R(N,M)=0$ for all $i<n$ and every nontrivial finitely generated $N$ with $\operatorname{Supp}N\subseteq V(I)$;
--   2. $\operatorname{Ext}^i_R(R/I,M)=0$ for all $i<n$;
--   3. $\operatorname{Ext}^i_R(N,M)=0$ for all $i<n$ for some nontrivial finitely generated $N$ with $\operatorname{Supp}N=V(I)$;
--   4. there is an $M$-regular sequence of length $n$ in $I$.
--
--   Rees proved this in 1956. It shows that the $I$-depth of $M$ (the length of a maximal $M$-regular sequence in $I$) is the smallest $i$ with $\operatorname{Ext}^i_R(R/I,M)\ne0$. This homological description of depth underlies the theory of Cohen–Macaulay rings and the Auslander–Buchsbaum formula.
--
--   **Formalization note.** Mathlib's `ModuleCat.exists_isRegular_tfae` (Matsumura, *Commutative Algebra*, Theorem 28). Modules are objects of `ModuleCat.{v} R` with `R` `v`-small. `CategoryTheory.Abelian.Ext N M i` is the $i$-th Ext group, and vanishing is `Subsingleton`. $R/I$ appears as `Shrink (R ⧸ I)` to fit the universe. `Module.support` is the support, `PrimeSpectrum.zeroLocus I` is $V(I)$, and `RingTheory.Sequence.IsRegular M rs` says that `rs` is an $M$-regular sequence.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ModuleCat.exists_isRegular_tfae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe v
open CategoryTheory

theorem rees_depth_theorem {R : Type*} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (hIM : I • (⊤ : Submodule R M) < ⊤) :
    List.TFAE [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
        Module.support R N ⊆ PrimeSpectrum.zeroLocus (I : Set R) → ∀ i < n, Subsingleton (Abelian.Ext N M i),
      ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus (I : Set R) ∧ ∀ i < n, Subsingleton (Abelian.Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs] := by sorry

end FamousTheorems
