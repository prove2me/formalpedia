-- Prove2me | Theorems.Thm_CliffordCert_Optimal_radical_splitting
-- name    : CliffordCert.Optimal.radical_splitting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:48.889501+00:00
-- url     : https://prove2.me/theorems/c1f0c6ae-46be-45e0-b146-c63035a9cb31
-- title:
--   Lemma 2 — radical splitting and paired-basis extension
-- statement:
--   Let $W$ be a subspace of a finite-dimensional binary symplectic space $(V,B)$. There is a nondegenerate subspace $U$ such that
--   $$W=U\oplus\operatorname{rad}(W).$$
--   The dimension of $U$ is even, and if $\dim W$ is even, then $\dim\operatorname{rad}(W)$ is even. Every nondegenerate subspace has a basis of pairs $e_i,f_i$ with $B(e_i,f_j)=\delta_{ij}$ and all $e,e$ and $f,f$ pairings zero. Every such paired basis extends to an ambient paired basis.
--
--   This supplies both parity and basis extension for the repair and Clifford statements.
--
--   Differences from the source:
--   - encoding: an arbitrary N-dimensional binary vector space → Fin N → ZMod 2 with an arbitrary alternating nondegenerate bilinear form when needed; reason: choosing coordinates is a linear isomorphism and changes no instance
--   - encoding: direct sum and extension of the paired basis → supremum plus disjointness of submodules and an injection of pair indices into an ambient basis; reason: these state internal direct sum and preserve each original basis vector
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 11, Lemma 2, Eq. (17) (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_symplectic
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem radical_splitting {N : ℕ} (B : Form N) (hB : IsSymplectic B)
    (W : Submodule F₂ (Binary N)) :
    (∃ U : Submodule F₂ (Binary N), U ⊔ radical B W = W ∧
      Disjoint U (radical B W) ∧ Nondegenerate B U ∧
      Even (Module.finrank F₂ U)) ∧
    (Even (Module.finrank F₂ W) → Even (Module.finrank F₂ (radical B W))) ∧
    (∀ S : Submodule F₂ (Binary N), Nondegenerate B S →
      ∃ h : ℕ, ∃ b : Module.Basis (Fin h ⊕ Fin h) F₂ S,
        Paired B (fun j => (b j).val)) ∧
    (∀ (S : Submodule F₂ (Binary N)) (h : ℕ)
      (b : Module.Basis (Fin h ⊕ Fin h) F₂ S),
      Paired B (fun j => (b j).val) →
      ∃ H : ℕ, ∃ c : Module.Basis (Fin H ⊕ Fin H) F₂ (Binary N),
      ∃ e : Fin h ↪ Fin H, Paired B c ∧
        (∀ i, c (.inl (e i)) = (b (.inl i)).val) ∧
        (∀ i, c (.inr (e i)) = (b (.inr i)).val)) := by sorry
end CliffordCert.Optimal
