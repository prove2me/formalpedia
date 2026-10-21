-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_lemma_15
-- name    : EFXGenVal.TwoVal.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:57.92199+00:00
-- url     : https://prove2.me/theorems/392781a2-976c-43dc-998a-44cd798a8fef
-- title:
--   Lemma 15, p. 12 — a semi-EFX allocation can be trimmed to an EFX allocation fixing N_a and b_0
-- statement:
--   Let the agents have normalized, monotone, non-degenerate valuations, each agent having one of two valuations: $v_a$ on the class $N_a$ and $v_b$ on the class $N_b=N\setminus N_a$. Let $X$ be a semi-EFX allocation (no agent of $N_a$ EFX envies anyone, and no agent of $N_b$ EFX envies an agent of $N_a$), and let $b_0\in N_b$ have the strictly smallest $v_b$-value among $N_b$:
--   $$X_{b_0}<_b X_{b}\qquad\text{for every } b\in N_b\setminus\{b_0\}.$$
--   Then there is an EFX allocation $Y$ with $Y_{a}=X_{a}$ for every $a\in N_a$ and $Y_{b_0}=X_{b_0}$.
--
--   In the proof of Theorem 14 this lemma turns the intermediate semi-EFX allocations into EFX allocations without touching the bundles that the partition leximin potential compares first.
--
--   **Formalization Note** The page assumes the chain $X_{b_0}<_bX_{b_1}<_b\cdots<_bX_{b_t}$. Only the part naming $b_0$ is kept, namely that $b_0$ is the strict $v_b$-minimum of $N_b$. The full chain implies this, so the statement here is at least as strong as the page's. The classes are a finset `A` of agents with `v i = va` on `A` and `v i = vb` off `A`. $Y$ is required to be an allocation, i.e. to have pairwise disjoint bundles.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, §4, Lemma 15, p. 12

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem lemma_15 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v) (hnd : IsNonDegenerate v)
    (va vb : Finset (Fin m) → ℝ) (A : Finset (Fin n))
    (hA : ∀ i ∈ A, v i = va) (hB : ∀ i ∉ A, v i = vb)
    (X : Fin n → Finset (Fin m)) (hX : IsPartialAllocation X)
    (b0 : Fin n) (hb0 : b0 ∉ A) (hmin : ∀ b ∉ A, b ≠ b0 → vb (X b0) < vb (X b))
    (hsemi : IsSemiEFX v A X) :
    ∃ Y : Fin n → Finset (Fin m), IsPartialAllocation Y ∧ IsEFX v Y ∧
      (∀ i ∈ A, Y i = X i) ∧ Y b0 = X b0 := by sorry

end EFXGenVal.TwoVal
