-- Prove2me | Theorems.Thm_EFXGenVal_TwoVal_lemma_18
-- name    : EFXGenVal.TwoVal.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:52.998572+00:00
-- url     : https://prove2.me/theorems/68dcbe5b-bd9c-40be-b111-ac596d13d80f
-- title:
--   Lemma 18, p. 25 — a small binary perturbation preserves strict preferences, is non-degenerate, and reflects EFX
-- statement:
--   Let agents $i\in N$ have normalized, monotone valuations $v_i:2^M\to\mathbb R$ over the items $M=\{g_0,\dots,g_{m-1}\}$. Let
--   $$\delta=\min_{i\in N}\ \min_{S,T:\,v_i(S)\neq v_i(T)} |v_i(S)-v_i(T)|,$$
--   and let $\varepsilon>0$ with $\varepsilon\cdot 2^m<\delta$. Define the perturbed valuations $v'_i(S)=v_i(S)+\varepsilon\sum_{g_j\in S}2^j$. Then:
--
--   1. for every agent $i$ and bundles $S,T$, $v_i(S)>v_i(T)$ implies $v'_i(S)>v'_i(T)$;
--   2. the perturbed instance is non-degenerate;
--   3. every EFX allocation for the perturbed valuations is an EFX allocation for the original ones.
--
--   This lemma lets the rest of the paper assume non-degenerate instances without loss of generality: an EFX allocation of the perturbed instance is one of the original instance.
--
--   **Formalization Note** The condition $\varepsilon\cdot 2^m<\delta$ is stated as: $\varepsilon\cdot 2^m<|v_i(S)-v_i(T)|$ whenever $v_i(S)\neq v_i(T)$. This is the same condition when such pairs exist, and it is vacuous when every $v_i$ is constant, where $\delta$ is a minimum over the empty set. Item $g_j$ is `j : Fin m`, so the weights are $2^0,\dots,2^{m-1}$. The third statement covers every allocation, complete or not, as on the page.
-- source:
--   Mahara, Extension of Additive Valuations to General Valuations on the Existence of EFX, arXiv:2107.09901v2, Appendix A, Lemma 18, p. 25

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_EFXGenVal_TwoVal_Setting

namespace EFXGenVal.TwoVal

open LittleCharity.EFX

theorem lemma_18 {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hnorm : IsNormalized v) (hmono : IsMonotoneVal v)
    (ε : ℝ) (hε : 0 < ε)
    (hδ : ∀ i S T, v i S ≠ v i T → ε * 2 ^ m < |v i S - v i T|) :
    (∀ i S T, v i T < v i S → perturb v ε i T < perturb v ε i S) ∧
      IsNonDegenerate (perturb v ε) ∧
      (∀ X : Fin n → Finset (Fin m), IsEFX (perturb v ε) X → IsEFX v X) := by sorry

end EFXGenVal.TwoVal
