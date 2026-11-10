-- Prove2me | Theorems.Thm_AlmostLinSubsetSum_Main_lemma_4_3
-- name    : AlmostLinSubsetSum.Main.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:29:06.144794+00:00
-- url     : https://prove2.me/theorems/52575d5d-c799-4d72-ae81-a60883439708
-- title:
--   Lemma 4.3 — the core: integer points of $\sum_{i\in I_G}[0,u_i]$ are subset sums of $\{u_i: i\in I_R\cup I_G\}$
-- statement:
--   **Lemma 4.3** (The Core, p. 18).
--   $$\Bigl(\sum_{i\in I_G}[0,u_i]\Bigr)\cap\mathbb Z^r\subseteq S\bigl(\{u_i : i\in I_R\cup I_G\}\bigr).$$
--
--   Setting (§4.1–4.2, with $I_0=\emptyset$ after reanchoring): $I_R,I_G$ are disjoint finite index sets; $\Gamma=\prod_{j=1}^r[-\gamma_j,\gamma_j]$ with integers $\gamma_j\ge1$; $u_i\in\Gamma\cap\mathbb Z^r$ for $i\in I_R\cup I_G$; and the subset sums of the reserve fill a box, (9): $\lambda\cdot\Gamma\cap\mathbb Z^r\subseteq S(\{u_i:i\in I_R\})$ for some real $\lambda\ge r$ (in the paper $\lambda=c_{\mathrm{gap}}h\ge r$ by Lemma 4.1). Subset sums are over index subsets, so repeated vectors count separately.
--
--   Differences from the source:
--   - generalization: the u_i, Γ, I_R, I_G produced by Theorem 4.2, with (9) for λ = c_gap·h after reanchoring (I_0 = ∅) → any disjoint finite I_R, I_G, any u_i ∈ Γ ∩ ℤ^r, and any real λ ≥ r with λ·Γ ∩ ℤ^r ⊆ S({u_i : i ∈ I_R}); reason: the proof uses only these facts; the paper's data satisfy them, as c_gap·h ≥ r by Lemma 4.1
--   - encoding: the multiset {u_i : i ∈ I_R ∪ I_G} → a family u : ι → ℤ^r with finite index sets, subset sums over index subsets Y ⊆ I_R ∪ I_G; reason: sub-multisets are index subsets
-- source:
--   Chen, Mao, Zhang (2026), An Almost-Linear Time Algorithm for Multidimensional Subset Sum, STOC 2027 submission, SHA-256 0cd42ca048cfff088013ad06450a278a6df72a29004c48c5c138f3f6df85d1e0, Lemma 4.3, p. 18

import Mathlib
import Definitions.Def_AlmostLinSubsetSum_Main_Basic

set_option autoImplicit false

namespace AlmostLinSubsetSum.Main

/-- **Lemma 4.3** (The Core; Chen, Mao, Zhang 2026, p. 18).
`(Σ_{i ∈ I_G} [0, u_i]) ∩ ℤ^r ⊆ S({u_i : i ∈ I_R ∪ I_G})`.

Stated in the setting of §4.1–4.2 after reanchoring (`I₀ = ∅`): disjoint finite index sets
`I_R` (reserve) and `I_G`; a box `Γ = ∏_j [−γ_j, γ_j]` with integers `γ_j ≥ 1`; vectors
`u_i ∈ Γ ∩ ℤ^r`; and the filled box (9): `λ · Γ ∩ ℤ^r ⊆ S({u_i : i ∈ I_R})` for some
`λ ≥ r` (the paper has `λ = c_gap h ≥ r`, by Lemma 4.1). Subset sums are over index subsets,
so repeated vectors count separately. -/
theorem lemma_4_3 {ι : Type*} [DecidableEq ι] {r : ℕ} (u : ι → Fin r → ℤ)
    (IR IG : Finset ι) (hdisj : Disjoint IR IG)
    (γ : Fin r → ℕ) (hγ : ∀ j, 1 ≤ γ j)
    (hu : ∀ i ∈ IR ∪ IG, toReal (u i) ∈ box (fun j => (γ j : ℝ)))
    (lam : ℝ) (hlam : (r : ℝ) ≤ lam)
    (hfill : ∀ z : Fin r → ℤ, toReal z ∈ dilate lam (box (fun j => (γ j : ℝ))) →
      z ∈ subsetSums IR u) :
    ∀ z : Fin r → ℤ, toReal z ∈ zonotope IG (fun i => toReal (u i)) →
      z ∈ subsetSums (IR ∪ IG) u := by sorry

end AlmostLinSubsetSum.Main
